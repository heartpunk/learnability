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

Memory regions are extracted from CLE's loaded view of the binary — the same
loader that provides virtual-address → file-bytes mapping for pyvex.  For
relocatable objects (.o files), CLE rebases sections and creates an ExternObject
for unresolved symbols (GOT-like).  The regions array captures every mapped
region so the pipeline can determine which constant addresses are in which
region (non-overlapping by CLE construction).
"""
from __future__ import annotations

import argparse
import json

import angr


def extract_memory_regions(project: "angr.Project") -> list[dict]:
    """Extract all mapped memory regions from CLE's loaded view.

    Returns a list of {name, vaddr, size, flags} dicts for every ALLOC
    section in the main object plus the ExternObject (if present).
    Regions are non-overlapping by CLE construction.
    """
    regions = []
    obj = project.loader.main_object
    for sec in obj.sections:
        if not sec.occupies_memory:
            continue
        flags = ""
        if sec.is_readable:
            flags += "r"
        if sec.is_writable:
            flags += "w"
        if sec.is_executable:
            flags += "x"
        regions.append({
            "name": sec.name,
            "vaddr": f"0x{sec.vaddr:x}",
            "size": sec.memsize,
            "flags": flags,
        })
    # ExternObject: CLE's synthetic GOT for unresolved relocations
    for o in project.loader.all_objects:
        if type(o).__name__ == "ExternObject" and o.min_addr < o.max_addr:
            regions.append({
                "name": "extern",
                "vaddr": f"0x{o.min_addr:x}",
                "size": o.max_addr - o.min_addr,
                "flags": "rw",
            })
            break
    return regions


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

    return {
        "arch": "amd64",
        "memory_regions": extract_memory_regions(project),
        "blocks": blocks,
    }


def extract_text_section(binary: str) -> dict:
    """Sweep the entire .text section of an ELF binary."""
    project = angr.Project(binary, auto_load_libs=False)
    obj = project.loader.main_object

    text = obj.sections_map.get(".text")
    if text is None:
        raise ValueError("No .text section found in binary")

    result = extract_linear(binary, text.min_addr, text.memsize)
    # extract_linear already includes regions from its own project, but
    # it creates a second project internally.  Override with ours.
    result["memory_regions"] = extract_memory_regions(project)
    return result


def extract_per_function(binary: str) -> dict:
    """Sweep each STT_FUNC symbol individually, producing per-function JSON.

    Uses CLE's rebased symbol addresses so block addresses match function
    entry points.  Output format matches loadFunctionsFromJSON in Lean:
        {"arch": "amd64", "functions": {"name": {"addr": "0x...", "size": N,
         "blocks": [...]}}, "memory_regions": [...]}
    """
    project = angr.Project(binary, auto_load_libs=False)
    obj = project.loader.main_object

    # Collect best name per address (prefer GLOBAL over LOCAL, shorter over longer)
    best_sym: dict[int, "cle.backends.symbol.Symbol"] = {}
    for sym in obj.symbols:
        if not sym.is_function or sym.size == 0:
            continue
        addr = sym.rebased_addr
        if addr not in best_sym:
            best_sym[addr] = sym
        else:
            prev = best_sym[addr]
            # Prefer GLOBAL binding, then shorter name (avoids .localalias)
            if sym.is_export and not prev.is_export:
                best_sym[addr] = sym
            elif sym.is_export == prev.is_export and len(sym.name) < len(prev.name):
                best_sym[addr] = sym

    functions = {}
    for addr, sym in sorted(best_sym.items()):
        blocks = []
        cursor = addr
        while cursor < addr + sym.size:
            block = project.factory.block(cursor)
            irsb = block.vex
            blocks.append(str(irsb))
            if block.size == 0:
                break
            cursor += block.size
        functions[sym.name] = {
            "addr": f"0x{addr:x}",
            "size": sym.size,
            "blocks": blocks,
        }

    return {
        "arch": "amd64",
        "functions": functions,
        "memory_regions": extract_memory_regions(project),
    }


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
        "--per-function",
        action="store_true",
        help="Sweep each ELF function symbol individually (per-function JSON)",
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

    if args.per_function:
        result = extract_per_function(args.binary)
    elif args.text:
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
