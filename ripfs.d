import core.stdc.errno;
import core.sys.posix.sys.stat;
import core.sys.posix.unistd;

import std.algorithm, std.conv, std.stdio;
import std.array;
import std.digest;
import std.digest.md : MD5;
import std.exception;
import std.file;
import std.path;
import std.range;
import std.string;
import std.traits;

import c.fuse.fuse;

import chunker;
import chunker.polynomials;

import ae.sys.file;
import ae.utils.array;
import ae.utils.funopt;
import ae.utils.main;

pragma(lib, "fuse");

alias Digest = MD5;
alias Hash = ReturnType!(Digest.finish);

align(1)
struct Reference
{
align(1):
	Hash hash; // to blob
	ulong offset;
	ulong length;
}

align(1)
struct VerbatimHeader
{
align(1):
	ulong length;
}

enum ChunkType : ubyte
{
	/// Raw data until EOF (deduplicate this later)
	/// Followed by raw bytes.
	raw,

	/// Reference to blob store
	/// Followed by a Reference.
	reference,

	/// Verbatim data (data that could not be deduplicated)
	/// Followed by a VerbatimHeader, and then by raw bytes.
	verbatim,
}

string hashPath(ref Hash hash)
{
	return format!"%02x/%02x/%-(%02x%)"(hash[0], hash[1], hash[2..$]);
}

__gshared string storePath;

/// Parse a deduplicated file.
const(ubyte)[] parse(const(ubyte)[] data)
{
	ubyte[] result;
	while (data.length)
	{
		auto type = cast(ChunkType)data.shift;
		switch (type)
		{
			case ChunkType.raw:
				enforce(!result, "Raw chunk type is only allowed at the start of the file");
				return data;
			case ChunkType.reference:
			{
				enforce(data.length >= Reference.sizeof, "Not enough data in file for Reference");
				auto reference = (cast(Reference[1])data.shift!(Reference.sizeof))[0];
				auto f = storePath
					.buildPath("blobs", hashPath(reference.hash))
					.File("rb");
				f.seek(reference.offset);

				auto targetStart = result.length;
				result.length += reference.length;
				auto bytesRead = f.rawRead(result[targetStart .. $]);
				enforce(bytesRead.length == reference.length, "EOF in blob");
				break;
			}
			case ChunkType.verbatim:
			{
				enforce(data.length >= VerbatimHeader.sizeof, "Not enough data in file for Verbatim");
				auto verbatim = (cast(VerbatimHeader[1])data.shift!(VerbatimHeader.sizeof))[0];

				enforce(data.length >= verbatim.length, "Not enough data in file for verbatim bytes");
				result ~= data.shift(verbatim.length);
				break;
			}
			default:
				throw new Exception("Unknown chunk type - data corruption");
		}
	}
	return result;
}

/// Compute the length of a deduplicated file.
size_t getLength(const(ubyte)[] data)
{
	size_t result;
	while (data.length)
	{
		auto type = cast(ChunkType)data.shift;
		switch (type)
		{
			case ChunkType.raw:
				enforce(!result, "Raw chunk type is only allowed at the start of the file");
				return data.length;
			case ChunkType.reference:
			{
				enforce(data.length >= Reference.sizeof, "Not enough data in file for Reference");
				auto reference = (cast(Reference[1])data.shift!(Reference.sizeof))[0];
				result += reference.length;
				break;
			}
			case ChunkType.verbatim:
			{
				enforce(data.length >= VerbatimHeader.sizeof, "Not enough data in file for Verbatim");
				auto verbatim = (cast(VerbatimHeader[1])data.shift!(VerbatimHeader.sizeof))[0];

				enforce(data.length >= verbatim.length, "Not enough data in file for verbatim bytes");
				data.shift(verbatim.length);
				result += verbatim.length;
				break;
			}
			default:
				throw new Exception("Unknown chunk type - data corruption");
		}
	}
	return result;
}

/// Deduplicate a file, if needed.
const(ubyte)[] deduplicate(const(ubyte)[] data)
{
	assert(data[0] == ChunkType.raw);
	data = data[1 .. $];

	// First, split into content-dependent chunks

	struct Chunk
	{
		Hash hash;
		ulong offset;
		ulong length;
	}
	Chunk[] chunks;

	{
		static ubyte[] buf;
		if (!buf)
			buf = new ubyte[8*1024*1024];

		ulong offset = 0;
		foreach (chunk; (cast(ubyte[])data).only.byCDChunk(Pol(0x3DA3358B4DC173), buf))
		{
			auto hash = digest!Digest(chunk.data);
			chunks ~= Chunk(hash, offset, chunk.data.length);
			offset += chunk.data.length;
		}
	}

	// Next, check our database and collect all hits.
	// NOTE: this is currently over-engineered, with the current deduplication policy
	// there will never be more than one hit per chunk.

	struct Hit
	{
		Hash blobHash;
		long delta; // (our file offset) - (blob file offset)
	}
	struct HitExtent
	{
		ulong start, end; // in file
		@property ulong length() { return end - start; }
	}
	HitExtent[Hit] hits;

	foreach (ref chunk; chunks)
	{
		Reference[] references;
		auto chunkPath = storePath
			.buildPath("chunks", hashPath(chunk.hash));
		if (chunkPath.exists)
			references = cast(Reference[])chunkPath.read;

		foreach (ref reference; references)
		{
			auto hit = Hit(reference.hash, chunk.offset - reference.offset);
			hits.require(hit, {
				HitExtent extent;

				auto blobData = storePath.buildPath("blobs", hashPath(reference.hash)).read.bytes;

				// Returns offset in blob of the last matching byte in the given direction.
				ulong scan(byte dir)()
				{
					long filePos = chunk.offset;
					@property long blobPos() { return filePos - hit.delta; }

					while (true)
					{
						bool fileDone = (dir < 0) ? filePos < 0 : filePos >=     data.length;
						bool blobDone = (dir < 0) ? blobPos < 0 : blobPos >= blobData.length;
						if (fileDone || blobDone)
							return filePos - dir;
						ubyte fileByte = /*fileDone ? 0 :*/     data[filePos];
						ubyte blobByte = /*blobDone ? 0 :*/ blobData[blobPos];
						if (fileByte != blobByte)
							return filePos - dir;
						filePos += dir;
					}
				}

				extent.start = scan!(-1);
				extent.end   = scan!(+1) + 1;

				return extent;
			}());
		}
	}

	Hit bestHit;
	ulong bestLength = 0;
	foreach (hit, extent; hits)
		if (extent.length > bestLength)
		{
			bestLength = extent.length;
			bestHit = hit;
		}

	if (bestLength < (Reference.sizeof - VerbatimHeader.sizeof))
	{
		// No good hits - save new blob
		auto blobHash = digest!Digest(data);
		auto blobPath = storePath.buildPath("blobs", hashPath(blobHash));
		blobPath.ensurePathExists();
		blobPath.atomicWrite(data);

		foreach (ref chunk; chunks)
		{
			auto chunkPath = storePath
				.buildPath("chunks", hashPath(chunk.hash));
			chunkPath.ensurePathExists();
			auto reference = Reference(blobHash, chunk.offset, chunk.length);
			auto f = File(chunkPath, "ab");
			f.rawWrite(reference.toArray);
		}

		ubyte[] result;
		result ~= ChunkType.reference;
		result ~= [Reference(blobHash, 0, data.length)].bytes;
		return result;
	}

	{
		auto bestExtent = hits[bestHit];
		auto fileStart = bestExtent.start;
		auto fileEnd   = bestExtent.end  ;
		auto blobStart = fileStart - bestHit.delta;
		auto blobEnd   = fileEnd   - bestHit.delta;

		ubyte[] result;

		if (fileStart > 0)
		{
			result ~= ChunkType.verbatim;
			VerbatimHeader header;
			header.length = fileStart;
			result ~= header.bytes;
			result ~= data[0 .. fileStart];
		}

		result ~= ChunkType.reference;
		Reference reference;
		reference.hash = bestHit.blobHash;
		reference.offset = blobStart;
		reference.length = blobEnd - blobStart;
		result ~= reference.bytes;

		if (fileEnd < data.length)
		{
			result ~= ChunkType.verbatim;
			VerbatimHeader header;
			header.length = data.length - fileEnd;
			result ~= header.bytes;
			result ~= data[fileEnd .. $];
		}

		return result;
	}
}

void deduplicatePath(string path)
{
	auto data = path.read.bytes;
	if (!data.length || data[0] != ChunkType.raw)
		return; // Doesn't need to be deduplicated

	atomicWrite(path, deduplicate(data));
}

string filePath(const char* c_path)
{
	auto path = c_path.fromStringz;
	enforce(path.startsWith("/"), new ErrnoException("Malformed FUSE path", EINVAL));
	return storePath ~ "/files" ~ cast(string)path;
}

/// Returns a writable File for a FUSE path, assuming it points to a raw file.
File rawFile(const char* c_path)
{
	auto realPath = c_path.filePath();

	if (realPath.isSymlink)
		throw new ErrnoException("Can't write through a symlink", EROFS);

	auto f = File(realPath, "r+b");
	ChunkType[1] chunkType;
	enforce(f.rawRead(chunkType[]).length == 1, "Empty file");
	enforce(chunkType[0] == ChunkType.raw,
		new ErrnoException("File already deduplicated", EROFS));
	return f;
}

int fuseWrap(scope int delegate() dg) nothrow
{
	try
		return dg();
	catch (ErrnoException e)
		return -e.errno;
	catch (FileException e)
		return -e.errno;
	catch (Exception e)
		return -EIO;
}

int fuseWrap(scope void delegate() dg) nothrow
{
	return fuseWrap({ dg(); return 0; });
}

extern(C) nothrow
{
	int fs_getattr(const char* c_path, stat_t* s)
    {
		return fuseWrap({
			auto realPath = c_path.filePath();
			errnoEnforce(lstat(realPath.toStringz, s) == 0, "lstat");

			if (S_ISREG(s.st_mode))
				s.st_size = parse(realPath.read.bytes).length;
		});
    }

	int fs_read(const char* c_path, char* buf_ptr, size_t size, off_t offset, fuse_file_info* fi)
    {
		return fuseWrap({
			auto unparsedData = c_path.filePath().read().bytes;
			auto parsedData = unparsedData.parse();
			if (offset >= parsedData.length)
				return 0;
			auto bytesRead = min(size, parsedData.length - offset);
			buf_ptr[0 .. bytesRead] = cast(char[])parsedData[offset .. offset + bytesRead];
			return bytesRead.to!int;
		});
    }

    int fs_write(const char* c_path, char* data_ptr, size_t size, off_t offset, fuse_file_info* fi)
	{
		return fuseWrap({
			auto f = c_path.rawFile();
			f.seek(1 + offset);
			f.rawWrite(data_ptr[0 .. size]);
			return size.to!int;
		});
	}

	int fs_truncate(const char* c_path, long length)
	{
		return fuseWrap({
			enforce(length >= 0, new ErrnoException("Bad length", EINVAL));
			File f = c_path.rawFile();
			f.flush();
			ftruncate(f.fileno, 1 + length);
		});
	}

    int fs_readdir(const char* c_path, void* buf, 
		fuse_fill_dir_t filler, off_t /*offset*/, fuse_file_info* fi)
    {
		return fuseWrap({
			foreach (de; c_path.filePath.dirEntries(SpanMode.shallow))
				filler(buf, cast(char*)de.name.baseName.toStringz, null, 0);
		});
    }

	int fs_readlink(const char* c_path, char* buf_ptr, size_t size)
	{
		return fuseWrap({
			auto result = readlink(c_path.filePath().toStringz, buf_ptr, size);
			if (result < 0)
				return -errno;
			return result.to!int;
		});
	}

    int fs_access(const char* c_path, int mode)
    {
		return fuseWrap({
			return access(c_path.filePath().toStringz, mode);
		});
    }

    int fs_mknod(const char* c_path, uint mod, ulong dev)
    {
		return fuseWrap({
			enforce(mod == octal!100640 && dev == 0, new ErrnoException("Unsupported mode", EOPNOTSUPP));
			auto realPath = c_path.filePath();
			auto f = File(realPath, "wb");
			ChunkType[1] chunkType = [ChunkType.raw];
			f.rawWrite(chunkType[]);
		});
    }

	int fs_unlink(const char* c_path)
	{
		return fuseWrap({
			c_path.filePath().remove();
		});
	}

	int fs_mkdir(const char* c_path, uint mode)
	{
		return fuseWrap({
			errnoEnforce(mkdir(c_path.filePath().toStringz, mode) == 0, "mkdir");
		});
	}

	int fs_rmdir(const char* c_path)
	{
		return fuseWrap({
			c_path.filePath().rmdir();
		});
	}

    int fs_rename(const char* c_orig, const char* c_dest)
    {
		return fuseWrap({
			auto destPath = c_dest.filePath();

			c_orig.filePath().rename(destPath);

			if (!isSymlink(destPath) && isFile(destPath))
				deduplicatePath(destPath);
		});
    }
}

int ripfs(
	Parameter!(string, "Directory path where ripfs should store its data.") storePath,
	Parameter!(string, "Directory path where the ripfs virtual filesystem should be created.") mountPath,
	Switch!("Run in foreground.", 'f') foreground = false,
	Option!(string[], "Additional FUSE options (e.g. debug).", "STR", 'o') options = null,
)
{
	.storePath = storePath;

	fuse_operations fsops;
	fsops.access = &fs_access;
	fsops.readdir = &fs_readdir;
	fsops.getattr = &fs_getattr;
	fsops.truncate = &fs_truncate;
	fsops.readlink = &fs_readlink;
	fsops.read = &fs_read;
	fsops.write = &fs_write;
	fsops.mknod = &fs_mknod;
	fsops.unlink = &fs_unlink;
	fsops.mkdir = &fs_mkdir;
	fsops.rmdir = &fs_rmdir;
	fsops.rename = &fs_rename;

	options ~= ["big_writes"]; // Essentially required, otherwise FUSE will use 4K writes and cause abysmal performance

	string[] args = ["ripfs", mountPath, "-o%-(%s,%)".format(options)];
	args ~= "-s"; // single-threaded
	if (foreground)
		args ~= "-f";
	auto c_args = new char*[args.length];
	foreach (i, arg; args)
		c_args[i] = cast(char*)arg.toStringz;
	auto f_args = FUSE_ARGS_INIT(cast(int)c_args.length, c_args.ptr);

	stderr.writeln("Starting FUSE filesystem.");
	scope(success) stderr.writeln("ripfs exiting.");
	return fuse_main(f_args.argc, f_args.argv, &fsops, null);
}

mixin main!(funopt!ripfs);
