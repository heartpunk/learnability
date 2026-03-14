#!/usr/bin/env python3
"""Extract VEX IR blocks via pyvex linear sweep.

Lifts bytes one block at a time using pyvex, advancing by irsb.size after
each block. No control flow analysis, no successor tracking — equivalent
to what objdump does for assembly.

Trust boundary: pyvex for VEX IR lifting. angr is used ONLY as an ELF loader
(virtual-address → file-bytes mapping) — no CFGFast, no analysis, no successor
tracking. All block-boundary decisions come from pyvex.size.

Modes:
    --func ADDR --size BYTES    Sweep a single function (original mode)
    --text                      Sweep entire .text section (whole-binary mode)
    --start ADDR --end ADDR     Sweep an address range

Output (stdout):
    {"arch": "amd64", "blocks": ["IRSB {\\n   ...\\n}", ...]}
"""
from __future__ import annotations

import argparse
import json

import angr


def extract_linear(binary: str, func_addr: int, func_size: int) -> dict:
    # angr.Project used ONLY for ELF loading — maps virtual addresses to file bytes.
    # No CFGFast, no analysis, no successor tracking.
    project = angr.Project(binary, auto_load_libs=False)

    addr = func_addr
    blocks = []
    while addr < func_addr + func_size:
        # factory.block calls pyvex at `addr`; pyvex stops at first branch.
        block = project.factory.block(addr)
        irsb = block.vex
        blocks.append(str(irsb))
        if block.size == 0:
            raise ValueError(
                f"pyvex returned zero-size block at 0x{addr:x} — cannot advance"
            )
        addr += block.size

    return {"arch": "amd64", "blocks": blocks}


def extract_text_section(binary: str) -> dict:
    """Sweep the entire .text section of an ELF binary."""
    project = angr.Project(binary, auto_load_libs=False)
    obj = project.loader.main_object

    text = obj.sections_map.get(".text")
    if text is None:
        raise ValueError("No .text section found in binary")

    return extract_linear(binary, text.min_addr, text.memsize)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract VEX IR blocks via pyvex linear sweep."
    )
    parser.add_argument("binary", help="Path to the binary to analyse")
    parser.add_argument(
        "--func",
        type=lambda s: int(s, 0),
        help="Function start address (hex or decimal)",
    )
    parser.add_argument(
        "--size",
        type=lambda s: int(s, 0),
        help="Function size in bytes (from ELF symbol table or objdump)",
    )
    parser.add_argument(
        "--text",
        action="store_true",
        help="Sweep entire .text section",
    )
    parser.add_argument(
        "--start",
        type=lambda s: int(s, 0),
        help="Start address for range sweep (hex or decimal)",
    )
    parser.add_argument(
        "--end",
        type=lambda s: int(s, 0),
        help="End address for range sweep (hex or decimal)",
    )
    args = parser.parse_args()

    if args.text:
        result = extract_text_section(args.binary)
    elif args.start is not None and args.end is not None:
        if args.end <= args.start:
            parser.error(f"--end (0x{args.end:x}) must be greater than --start (0x{args.start:x})")
        result = extract_linear(args.binary, args.start, args.end - args.start)
    elif args.func is not None and args.size is not None:
        result = extract_linear(args.binary, args.func, args.size)
    else:
        parser.error(
            "Provide --text, --start/--end, or --func/--size"
        )

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
