# ripfs integration test script

import shlex

STORE = "/home/alice/store"
MNT = "/home/alice/mnt"


def run(cmd):
    """Run a command as the unprivileged user, and return its output."""
    return machine.succeed(f"su alice -c {shlex.quote(cmd)}")


def run_fail(cmd):
    machine.fail(f"su alice -c {shlex.quote(cmd)}")


def mount():
    run(f"mkdir -p {MNT}")
    # Without -f, ripfs daemonizes once the filesystem is mounted.
    run(f"ripfs {STORE} {MNT}")
    run(f"mountpoint {MNT}")


def unmount():
    run(f"fusermount3 -u {MNT}")
    machine.wait_until_fails(f"su alice -c {shlex.quote(f'mountpoint {MNT}')}")


def real_size(path):
    return int(run(f"stat -c %s {STORE}/files/{path}").strip())


def test_basic_operations():
    run(f"echo 'hello world' > {MNT}/hello.txt")
    output = run(f"cat {MNT}/hello.txt")
    assert output == "hello world\n", f"Unexpected contents: {output!r}"

    run(f"echo 'more' >> {MNT}/hello.txt")
    output = run(f"cat {MNT}/hello.txt")
    assert output == "hello world\nmore\n", f"Unexpected contents: {output!r}"

    run(f"truncate -s 5 {MNT}/hello.txt")
    output = run(f"cat {MNT}/hello.txt")
    assert output == "hello", f"Unexpected contents after truncate: {output!r}"

    run(f"chmod 600 {MNT}/hello.txt")
    mode = run(f"stat -c %a {MNT}/hello.txt").strip()
    assert mode == "600", f"Unexpected mode: {mode}"

    run(f"touch -d '2020-01-02 03:04:05' {MNT}/hello.txt")
    mtime = run(f"stat -c %Y {MNT}/hello.txt").strip()
    expected = run("date -d '2020-01-02 03:04:05' +%s").strip()
    assert mtime == expected, f"Unexpected mtime: {mtime} != {expected}"

    run(f"mkdir {MNT}/dir")
    run(f"echo x > {MNT}/dir/f")
    listing = run(f"ls {MNT}/dir").split()
    assert listing == ["f"], f"Unexpected listing: {listing}"
    run_fail(f"rmdir {MNT}/dir")  # not empty
    run(f"rm {MNT}/dir/f")
    run(f"rmdir {MNT}/dir")
    run(f"rm {MNT}/hello.txt")
    run_fail(f"test -e {MNT}/hello.txt")

    # rename(2) flags (here RENAME_EXCHANGE) are not supported, and must
    # fail rather than be treated as a plain (overwriting) rename.
    run(f"echo a > {MNT}/a && echo b > {MNT}/b")
    run_fail(f"mv --exchange {MNT}/a {MNT}/b")
    output = run(f"cat {MNT}/a {MNT}/b")
    assert output == "a\nb\n", f"Unexpected contents after failed exchange: {output!r}"
    run(f"rm {MNT}/a {MNT}/b")


def test_deduplication():
    # A "song", and a "recording" containing it between unique cross-fades.
    run("head -c 4M /dev/urandom > $HOME/song")
    run("head -c 64K /dev/urandom > $HOME/pre")
    run("head -c 64K /dev/urandom > $HOME/post")
    run("cat $HOME/pre $HOME/song $HOME/post > $HOME/recording")

    # Files are deduplicated when renamed into place.
    run(f"cp $HOME/song {MNT}/song.tmp && mv {MNT}/song.tmp {MNT}/song")
    run(f"cp $HOME/recording {MNT}/recording.tmp && mv {MNT}/recording.tmp {MNT}/recording")

    run(f"cmp $HOME/song {MNT}/song")
    run(f"cmp $HOME/recording {MNT}/recording")

    size = int(run(f"stat -c %s {MNT}/recording").strip())
    assert size == 4 * 1024 * 1024 + 2 * 64 * 1024, f"Unexpected virtual size: {size}"

    # The recording should be stored as the unique edges plus a reference.
    stored = real_size("recording")
    assert stored < 1024 * 1024, f"Recording not deduplicated ({stored} bytes stored)"


def test_persistence():
    unmount()
    mount()
    run(f"cmp $HOME/song {MNT}/song")
    run(f"cmp $HOME/recording {MNT}/recording")


# Main test sequence
machine.wait_for_unit("multi-user.target")

mount()
test_basic_operations()
test_deduplication()
test_persistence()
unmount()
