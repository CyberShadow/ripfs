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

import dfuse.fuse;

import chunker;
import chunker.polynomials;

import ae.sys.file;
import ae.utils.array;

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

final class RipFS : Operations
{
private:
	string storePath;

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

	string filePath(const(char)[] fusePath)
	{
		enforce(fusePath.startsWith("/"), new FuseException(ENOENT));
		return storePath ~ "/files" ~ cast(string)fusePath;
	}

	/// Returns a writable File for a FUSE path, assuming it points to a raw file.
	File rawFile(const(char)[] fusePath)
	{
		auto realPath = filePath(fusePath);

		if (realPath.isSymlink)
			throw new FuseException(EROFS);

		File f;
		try
			f.open(realPath, "r+b");
		catch (ErrnoException e)
			throw new FuseException(e.errno);
		ChunkType[1] chunkType;
		enforce(f.rawRead(chunkType[]).length == 1, "Empty file");
		enforce(chunkType[0] == ChunkType.raw, new FuseException(EROFS)); // File already deduplicated
		return f;
	}

public:
	this(string storePath)
	{
		this.storePath = storePath;

		auto filesPath = storePath.buildPath("files");
		if (!filesPath.exists)
		{
			stderr.writeln("Initializing RipFS store.");
			filesPath.mkdir();
			stderr.writeln("Initialization complete."); // :)
		}
	}

protected:
    override void getattr(const(char)[] path, ref stat_t s)
    {
		auto realPath = filePath(path);
		if (lstat(realPath.toStringz, &s) != 0)
			throw new FuseException(errno);

		if (S_ISREG(s.st_mode))
			s.st_size = parse(realPath.read.bytes).length;
    }

    override ulong read(const(char)[] path, ubyte[] buf, ulong offset)
    {
		ubyte[] unparsedData;
		try
			unparsedData = filePath(path).read.bytes;
		catch (FileException e)
			throw new FuseException(e.errno);

		auto parsedData = parse(unparsedData);
		if (offset >= parsedData.length)
			return 0;
		auto bytesRead = min(buf.length, parsedData.length - offset);
		buf[0 .. bytesRead] = parsedData[offset .. offset + bytesRead];
		return bytesRead;
    }

    override int write(const(char)[] path, in ubyte[] data, ulong offset)
	{
		auto f = rawFile(path);
		f.seek(1 + offset);
		f.rawWrite(data);
		return data.length.to!int;
	}

	override void truncate(const(char)[] path, ulong length)
	{
		File f = rawFile(path);
		f.flush();
		ftruncate(f.fileno, 1 + length);
	}

    override string[] readdir(const(char)[] path)
    {
		try
			return filePath(path)
				.dirEntries(SpanMode.shallow)
				.map!(de => de.name.baseName)
				.array;
		catch (FileException e)
			throw new FuseException(e.errno);
    }

	override size_t readlink(const(char)[] path, ubyte[] buf)
	{
		auto result = .readlink(filePath(path).toStringz, cast(char*)buf.ptr, buf.length);
		if (result < 0)
			throw new FuseException(errno);
		return result;
	}

    override bool access(const(char)[] path, int mode)
    {
		auto realPath = filePath(path);
		if (.access(realPath.toStringz, mode) != 0)
			throw new FuseException(errno);

		return true;
    }

    override void mknod(const(char)[] path, int mod, ulong dev)
    {
		enforce(mod == octal!100640 && dev == 0, new FuseException(EOPNOTSUPP));
		auto realPath = filePath(path);
		auto f = File(realPath, "wb");
		ChunkType[1] chunkType = [ChunkType.raw];
		f.rawWrite(chunkType[]);
    }

	override void unlink(const(char)[] path)
	{
		try
			filePath(path).remove();
		catch (FileException e)
			throw new FuseException(e.errno);
	}

	override void mkdir(const(char)[] path, uint mode)
	{
		if (.mkdir(filePath(path).toStringz, mode) != 0)
			throw new FuseException(errno);
	}

	override void rmdir(const(char)[] path)
	{
		if (.rmdir(filePath(path).toStringz) != 0)
			throw new FuseException(errno);
	}

    override void rename(const(char)[] orig, const(char)[] dest)
    {
		auto destPath = filePath(dest);

		try
			filePath(orig).rename(filePath(dest));
		catch (FileException e)
			throw new FuseException(e.errno);

		if (!isSymlink(destPath) && isFile(destPath))
			deduplicatePath(destPath);
    }

}

int main(string[] args)
{
	enforce(args.length >= 3, "Usage: " ~ args[0] ~ " STORE MOUNTPOINT [OPTIONS...]");

    auto fs = new Fuse("RipFS", true, false);
    fs.mount(new RipFS(args[1]), args[2], args[3 .. $]);

    return 0;
}
