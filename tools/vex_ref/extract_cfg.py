#!/usr/bin/env python3
"""Extract a function's CFG as a list of VEX IR text blocks.

Thin wrapper around angr/pyvex: lifts every basic block in the function
to VEX IR, serialises each IRSB as a plain text string, and emits JSON.

The Lean side (VexIRParser.parseProgram) consumes this output directly.

Usage:
    python extract_cfg.py BINARY --func ADDR
    python extract_cfg.py BINARY --func 0x401234

Output (stdout):
    {"arch": "amd64", "blocks": ["IRSB {\n   ...\n}", ...]}
"""
from __future__ import annotations

import argparse
import json

import angr


def extract_cfg(binary: str, func_addr: int) -> dict:
    project = angr.Project(binary, auto_load_libs=False)
    cfg = project.analyses.CFGFast(function_starts=[func_addr])
    func = cfg.functions[func_addr]
    blocks = []
    for block in func.blocks:
        irsb = project.factory.block(block.addr).vex
        blocks.append(str(irsb))
    return {"arch": "amd64", "blocks": blocks}


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract a function CFG as VEX IR text blocks (one IRSB string per block)."
    )
    parser.add_argument("binary", help="Path to the binary to analyse")
    parser.add_argument(
        "--func",
        type=lambda s: int(s, 0),
        required=True,
        help="Function start address (hex or decimal)",
    )
    args = parser.parse_args()
    result = extract_cfg(args.binary, args.func)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
