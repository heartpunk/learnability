#!/usr/bin/env python3
"""Extract a function's VEX IR blocks via linear sweep.

Lifts the function's bytes one block at a time using pyvex, advancing by
irsb.size after each block. No control flow analysis, no successor tracking —
equivalent to what objdump does for assembly.

Trust boundary: pyvex for VEX IR lifting. angr is used ONLY as an ELF loader
(virtual-address → file-bytes mapping) — no CFGFast, no analysis, no successor
tracking. All block-boundary decisions come from pyvex.size.

Usage:
    python extract_cfg.py BINARY --func ADDR --size BYTES
    python extract_cfg.py BINARY --func 0x40006f --size 908

Output (stdout):
    {"arch": "amd64", "blocks": ["IRSB {\n   ...\n}", ...]}
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


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract a function's VEX IR blocks via pyvex linear sweep."
    )
    parser.add_argument("binary", help="Path to the binary to analyse")
    parser.add_argument(
        "--func",
        type=lambda s: int(s, 0),
        required=True,
        help="Function start address (hex or decimal)",
    )
    parser.add_argument(
        "--size",
        type=lambda s: int(s, 0),
        required=True,
        help="Function size in bytes (from ELF symbol table or objdump)",
    )
    args = parser.parse_args()
    result = extract_linear(args.binary, args.func, args.size)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
