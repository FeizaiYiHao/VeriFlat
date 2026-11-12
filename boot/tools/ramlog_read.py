#!/usr/bin/env python3
"""Prints the RAM log that VeriFlat wrote with the boot option ramlog=<address> (see boot/ns16550a/src/ramlog.rs).

Usage: ramlog_read.py <file or device, e.g. /dev/pmem0 or a pmemsave dump>
It prints the header fields, then the log text; it exits with status 1 if the magic VFRAMLOG is missing.
"""

import struct
import sys

REASONS = {0: "running (no recorded end)", 1: "sys_debug_exit", 2: "kernel panic", 3: "loader panic", 4: "fatal exception", 5: "timeout (reset_after)"}


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__.strip())
    with open(sys.argv[1], "rb") as f:
        header = f.read(40)
        if len(header) < 40 or header[:8] != b"VFRAMLOG":
            print("%s: no VFRAMLOG magic" % sys.argv[1], file=sys.stderr)
            sys.exit(1)
        version, header_size, capacity, written, reason, code = struct.unpack_from("<IIQQII", header, 8)
        f.seek(header_size)
        text = f.read(min(written, capacity))
    print("version %d, header %d bytes, capacity %d bytes, written %d bytes%s" % (version, header_size, capacity, written, " (full)" if written >= capacity else ""))
    print("exit reason %d: %s, exit code %d" % (reason, REASONS.get(reason, "unknown"), code))
    print("----")
    sys.stdout.write(text.decode("utf-8", "replace"))
    if text and not text.endswith(b"\n"):
        sys.stdout.write("\n")


if __name__ == "__main__":
    main()
