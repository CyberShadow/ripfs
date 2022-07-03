import core.stdc.errno;
import core.sys.posix.fcntl;
import core.sys.posix.signal;
import core.sys.posix.sys.stat;
import core.sys.posix.unistd;

import std.algorithm.comparison;
import std.algorithm.iteration;
import std.algorithm.searching;
import std.algorithm.sorting;
import std.array;
import std.conv;
import std.datetime.systime;
import std.digest.md : MD5;
import std.digest;
import std.exception;
import std.file;
import std.internal.cstring;
import std.path;
import std.range;
import std.stdio : File, stderr;
import std.string;
import std.traits;

import c.fuse.fuse;

import chunker;
import chunker.polynomials;

import ae.sys.data;
import ae.sys.datamm;
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

/// Convert a hash to a fanned-out path fragment.
string hashPath(ref Hash hash)
{
	return format!"%02x/%02x/%-(%02x%)"(hash[0], hash[1], hash[2..$]);
}

__gshared
{
	string storePath;
	enum dedupThresholdDefault = 128 * 1024;
	ulong dedupThreshold;
}

ubyte[n] shift(size_t n)(ref Data data)
{
	if (data.length < n) assert(false);
	ubyte[n] result = data.contents.bytes[0 .. n];
	data = data[n .. $];
	return result;
}

Data shift(ref Data data, size_t n)
{
	if (data.length < n) assert(false);
	Data result = data[0 .. n];
	data = data[n .. $];
	return result;
}

ubyte shift(ref Data data) { return data.shift!1[0]; }

/// Parse a deduplicated file's contents.
DataVec parse(Data data)
{
	DataVec result;
	while (data.length)
	{
		auto type = cast(ChunkType)data.shift;
		switch (type)
		{
			case ChunkType.raw:
				enforce(!result, "Raw chunk type is only allowed at the start of the file");
				result ~= data;
				return result;
			case ChunkType.reference:
			{
				enforce(data.length >= Reference.sizeof, "Not enough data in file for Reference");
				auto reference = (cast(Reference[1])data.shift!(Reference.sizeof))[0];
				auto f = storePath
					.buildPath("blobs", hashPath(reference.hash))
					.mapFile(MmMode.read);
				f = f[reference.offset .. $];
				enforce(f.length >= reference.length, "EOF in blob");
				result ~= f[0 .. reference.length];
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

/// Compute the length of a deduplicated file's contents.
size_t getLength(Data data)
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

/// Deduplicate a file's contents.
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

				auto blobData = storePath.buildPath("blobs", hashPath(reference.hash)).read().bytes;

				// Returns offset in blob of the first mismatching byte in the given direction.
				ulong scan(byte dir)()
				{
					long filePos = chunk.offset;
					@property long blobPos() { return filePos - hit.delta; }

					static if (dir < 0)
						filePos += dir;

					while (true)
					{
						bool fileDone = (dir < 0) ? filePos < 0 : filePos >=     data.length;
						bool blobDone = (dir < 0) ? blobPos < 0 : blobPos >= blobData.length;
						if (fileDone || blobDone)
							return filePos;
						ubyte fileByte = /*fileDone ? 0 :*/     data[filePos];
						ubyte blobByte = /*blobDone ? 0 :*/ blobData[blobPos];
						if (fileByte != blobByte)
							return filePos - dir;
						filePos += dir;
					}
				}

				extent.start = scan!(-1) + 1;
				extent.end   = scan!(+1);

				return extent;
			}());
		}
	}

	// Sort hits, best (longest) first
	auto bestHits = hits
		.byKeyValue
		.array
		.sort!((a, b) => a.value.length > b.value.length)
		.release;

	// Map for which hit we are going to use for each byte.
	// hitMap[i] corresponds to bestHits[i-1].
	auto hitMap = new ubyte[data.length];

	if (bestHits.length > ubyte.max - 1)
		bestHits.length = ubyte.max - 1;

	// Use each hit for deduplication, if applicable.
	foreach (i, ref hit; bestHits)
	{
		auto start = hit.value.start;
		auto end   = hit.value.end;

		// Shrink off overlaps
		while (start < end && hitMap[start] != 0)
			start++;
		while (start < end && hitMap[end - 1] != 0)
			end--;

		// Note: The above scan doesn't handle "islands" (i.e. e.g. 000001111100000).
		// However, that shouldn't be possible due to the length sorting,
		// and even if it was, clobbering it is beneficial as
		// we will cover more with a single chunk.

		hitMap[start .. end] = (1 + i).to!ubyte;
	}

	debug stderr.writeln("Hits: ", hitMap.group);

	auto numUniqueBytes = hitMap.count!(b => b == 0);

	if (bestHits.length == 0 || numUniqueBytes > dedupThreshold)
	{
		// File could not be satisfactorily deduplicated - save new blob
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
		ubyte[] result;

		size_t offset = 0;
		foreach (g; hitMap.group)
		{
			ubyte mapIndex = g[0];
			ulong length = g[1];

			if (mapIndex == 0)
			{
				// Could not deduplicate - write verbatim chunk
				result ~= ChunkType.verbatim;
				VerbatimHeader header;
				header.length = length;
				result ~= header.bytes;
				result ~= data[offset .. offset + length];
			}
			else
			{
				auto hit = &bestHits[mapIndex - 1];

				auto fileStart = offset;
				auto fileEnd   = offset + length;

				auto blobStart = fileStart - hit.key.delta;
				auto blobEnd   = fileEnd   - hit.key.delta;

				result ~= ChunkType.reference;
				Reference reference;
				reference.hash = hit.key.blobHash;
				reference.offset = blobStart;
				reference.length = blobEnd - blobStart;
				result ~= reference.bytes;
			}

			offset += length;
		}

		return result;
	}
}

/// Deduplicate a file, if needed.
void deduplicatePath(string path)
{
	const(ubyte)[] data = path.read().bytes;
	if (!data.length || data[0] != ChunkType.raw)
		return; // Doesn't need to be deduplicated

	data = data.deduplicate();

	auto attributes = path.getAttributes();
	SysTime accessTime, modificationTime;
	path.getTimes(accessTime, modificationTime);

	auto tmpPath = path ~ ".ripfs-tmp";
	tmpPath.write(data);
	tmpPath.setTimes(accessTime, modificationTime);
	tmpPath.setAttributes(attributes);
	tmpPath.rename(path);
}

auto filePath(const char* c_path)
{
	auto path = c_path.fromStringz;
	enforce(path.skipOver("/"), new ErrnoException("Malformed FUSE path", EINVAL));
	return chainPath(storePath, "files", path);
}

/// Returns a writable File for a FUSE path, assuming it points to a raw file.
File rawFile(const char* c_path)
{
	auto realPath = c_path.filePath;

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
	{
		debug stderr.writeln(e).assumeWontThrow;
		return -e.errno;
	}
	catch (FileException e)
	{
		debug stderr.writeln(e).assumeWontThrow;
		return -e.errno;
	}
	catch (Exception e)
	{
		debug stderr.writeln(e).assumeWontThrow;
		return -EIO;
	}
}

int fuseWrap(scope void delegate() dg) nothrow
{
	return fuseWrap({ dg(); return 0; });
}

/// Calculate and fill in `s.st_size`.
void cachedGetSize(string realPathStr, stat_t* s)
{
	// So that we don't have to read the entire file on a `stat`,
	// cache virtual file size in an xattr.
	static struct CachedSize
	{
		// Key
		long mtime;
		ulong realSize;
		// Value
		ulong virtualSize;
	}

	try
	{
		auto cacheData = cast(ubyte[])realPathStr.xAttrs["user.ripfs.size"];
		enforce(cacheData.length == CachedSize.sizeof, "Size mismatch");
		auto cacheEntry = cacheData.fromBytes!CachedSize;
		enforce(cacheEntry.mtime == (*s).statTimeToStdTime!"m".stdTime, "Cache key mtime mismatch");
		enforce(cacheEntry.realSize == s.st_size, "Cache key size mismatch");

		// Cache hit
		s.st_size = cacheEntry.virtualSize;
	}
	catch (Exception)
	{
		// Cache miss or other error
		auto virtualSize = realPathStr.mapFile(MmMode.read).getLength();

		CachedSize cacheEntry;
		cacheEntry.mtime = (*s).statTimeToStdTime!"m".stdTime;
		cacheEntry.realSize = s.st_size;
		cacheEntry.virtualSize = virtualSize;

		s.st_size = cacheEntry.virtualSize;

		// Save
		try
			realPathStr.xAttrs["user.ripfs.size"] = cacheEntry.bytes;
		catch (Exception e) {} // xattrs not supported
	}
}

extern(C) nothrow
{
	int fs_getattr(const char* c_path, stat_t* s)
	{
		return fuseWrap({
			auto realPath = c_path.filePath;
			errnoEnforce(lstat(realPath.tempCString, s) == 0, "lstat");

			if (S_ISREG(s.st_mode))
				cachedGetSize(realPath.to!string, s);
		});
	}

	int fs_read(const char* c_path, char* buf_ptr, size_t size, off_t offset, fuse_file_info* fi)
	{
		return fuseWrap({
			auto unparsedData = c_path.filePath.to!string.mapFile(MmMode.read);
			auto parsedData = unparsedData.parse();
			auto parsedDataLength = parsedData[].map!((ref Data d) => d.length).sum;
			if (offset >= parsedDataLength)
				return 0;
			auto bytesRead = min(size, parsedDataLength - offset);
			size_t p = 0;
			foreach (ref datum; parsedData.bytes[offset .. offset + bytesRead])
			{
				buf_ptr[p .. p + datum.length] = cast(char[])datum.contents[];
				p += datum.length;
			}
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

	int fs_chmod(const char* c_path, uint mode)
	{
		return fuseWrap({
			errnoEnforce(chmod(c_path.filePath.tempCString, mode) == 0, "chmod");
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
			foreach (de; c_path.filePath.to!string.dirEntries(SpanMode.shallow))
				filler(buf, cast(char*)de.name.baseName.toStringz, null, 0);
		});
	}

	int fs_readlink(const char* c_path, char* buf_ptr, size_t size)
	{
		return fuseWrap({
			auto result = readlink(c_path.filePath.tempCString, buf_ptr, size);
			if (result < 0)
				return -errno;
			return result.to!int;
		});
	}

	int fs_access(const char* c_path, int mode)
	{
		return fuseWrap({
			return access(c_path.filePath.tempCString, mode);
		});
	}

	int fs_mknod(const char* c_path, uint mod, ulong dev)
	{
		return fuseWrap({
			enforce(S_ISREG(mod) && dev == 0, new ErrnoException("Unsupported mode", EOPNOTSUPP));
			auto realPath = c_path.filePath;
			{
				auto f = File(realPath, "wb");
				ChunkType[1] chunkType = [ChunkType.raw];
				f.rawWrite(chunkType[]);
			}
			errnoEnforce(chmod(realPath.tempCString, mod) == 0, "chmod");
		});
	}

	int fs_unlink(const char* c_path)
	{
		return fuseWrap({
			c_path.filePath.remove();
		});
	}

	int fs_mkdir(const char* c_path, uint mode)
	{
		return fuseWrap({
			errnoEnforce(mkdir(c_path.filePath.tempCString, mode) == 0, "mkdir");
		});
	}

	int fs_rmdir(const char* c_path)
	{
		return fuseWrap({
			c_path.filePath.rmdir();
		});
	}

	int fs_rename(const char* c_orig, const char* c_dest)
	{
		return fuseWrap({
			auto destPath = c_dest.filePath;

			c_orig.filePath.rename(destPath);

			if (!isSymlink(destPath) && isFile(destPath))
				deduplicatePath(destPath.to!string);
		});
	}

	int fs_utimens(const char* c_path, const ref timespec[2] t)
	{
		return fuseWrap({
			errnoEnforce(utimensat(AT_FDCWD, c_path.filePath.tempCString, t, 0) == 0, "utimensat");
		});
	}
}

int ripfs(
	Parameter!(string, "Directory path where ripfs should store its data.") storePath,
	Parameter!(string, "Directory path where the ripfs virtual filesystem should be created.") mountPath,
	Option!(ulong, "Allow at most this many unique bytes in deduplicated files before saving them as a reference blob.") dedupThreshold = dedupThresholdDefault,
	Switch!("Run in foreground.", 'f') foreground = false,
	Option!(string[], "Additional FUSE options (e.g. debug).", "STR", 'o') options = null,
)
{
	.storePath = storePath;
	.dedupThreshold = dedupThreshold;

	{
		auto filesPath = storePath.buildPath("files");
		if (!filesPath.exists)
		{
			stderr.writeln("Initializing RipFS store.");
			filesPath.mkdirRecurse();
			stderr.writeln("Initialization complete."); // :)
		}
	}

	fuse_operations fsops;
	fsops.getattr = &fs_getattr;
	fsops.readlink = &fs_readlink;
	fsops.mknod = &fs_mknod;
	fsops.mkdir = &fs_mkdir;
	fsops.unlink = &fs_unlink;
	fsops.rmdir = &fs_rmdir;
	// fsops.symlink = &fs_symlink;
	fsops.rename = &fs_rename;
	// fsops.link = &fs_link;
	fsops.chmod = &fs_chmod;
	// fsops.chown = &fs_chown;
	fsops.truncate = &fs_truncate;
	// fsops.open = &fs_open;
	fsops.read = &fs_read;
	fsops.write = &fs_write;
	// fsops.release = &fs_release;
	fsops.readdir = &fs_readdir;
	fsops.access = &fs_access;
	fsops.utimens = &fs_utimens;

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
