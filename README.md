ripfs
=====

ripfs is a simple deduplicating userspace filesystem designed to efficiently store recordings of Internet radio stations.


The problem
-----------

Internet radio stations generally continuously transmit items chosen from some set of audio segments (songs).
The set is finite, so items will be transmitted more than once (reruns, or just random selections from the DJ's playlist on "shuffle").
Regardless of previous order, items are usually "cross-faded", or otherwise modified (such that trivial perfect deduplication isn't possible).

Listeners may choose to record the stream to their machine, so that it can be played while offline, or e.g. to skip songs they don't like.
(Note that [legality of this varies](https://en.wikipedia.org/wiki/Radio_music_ripping#Legal_issues).)
In this case, users must make a choice with a compromise:

1. Perform crude deduplication on the recorded stream segments, e.g. deleting segments (songs) with duplicate names.

   - Downside: due to the cross-fading added by the station,
     segment beginnings and ends may now fade from/to segments that had been deduplicated and deleted,
     resulting in a jarring transition.

   - Downside: if the copy of the segment to keep is chosen arbitrarily,
     there is a risk that the chosen copy is imperfect,
     and uncorrupted "duplicates" are deleted.

2. Record the stream continuously, preserving the order and all transitions.

   - Downside: requires a significant and wasteful amount of disk space.


The solution
------------

ripfs attempts to provide the benefit of both of the above solutions by performing best-effort deduplication of new files.

When a new file is added to ripfs, the algorithm is as follows:

1. The file is split into [content-defined chunks](https://github.com/CyberShadow/chunker).

   Unlike classical block-based deduplication, this allows deduplicating even when the offsets don't match or are multiples of some power of two.

2. Calculate a hash for each chunk.

3. Search the database for previously encountered occurrences of these chunks.

4. Using these search results, find spans within the added file which match previously known blobs.

   Do this by taking a matching chunk, then extending its bounds in both directions for as long as the data continues to match.
   Use as many blobs as necessary to cover as much of the file as possible.

5. If sufficient matches are found, record the newly added file in a deduplicated form
   (usually verbatim unique data from the start of the file, followed by a reference to another blob, followed by verbatim unique data from the end of the file).

   If no satisfactory match is found, add the contents of the newly added file as a new blob and record the new file as a reference to the entire blob's contents.

Aside from the cross-fading effect at the start and end, and occasional corruption (silence/skips), transmissions seem to otherwise be bit-identical, requiring no decoding for deduplication. (If your Internet radio station does not have this property, the current implementation of ripfs will be insufficient for your case.)


Building
--------

- Install [a D compiler](https://dlang.org/download.html)
- Install [Dub](https://github.com/dlang/dub), if it wasn't included with your D compiler
- Run `dub build -b release`


Usage
-----

```shell
# 1. Create a directory for ripfs to store its database
$ mkdir ~/ripfs.store

# 2. Create a directory where ripfs will be mounted
$ mkdir ~/ripfs

# 3. Run ripfs
$ ripfs ~/ripfs.store ~/ripfs

# 4. Import existing recordings
# ripfs performs deduplication when a file is renamed,
# following the "create $f.tmp then rename $f.tmp to $f" pattern.
$ cd ~/music/recorded
$ for f in *.mp3 ; do cp -a "$f" ~/ripfs/"$f".tmp && mv ~/ripfs/"$f"{.tmp,} ; done

# 5. Save newly recorded segments to ripfs
# streamripper will place partial files in the "incomplete" directory
# and move them out when done, causing ripfs to deduplicate them at
# that point.
$ streamripper -d ~/ripfs ...
```
