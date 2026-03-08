# Opcode Backfill Lane: Width, No Flags

## Scope

Expand only within the already-supported no-flags, width-sensitive slice.

Good targets:
- more `mov r32, r32` zero-extending writes
- more `lea r32, [...]` zero-extending writes
- destination-register variants
- immediate/base/index variants that still lower into the current operators

## Allowed To Touch
- `tools/vex_ref/corpus_manifest.json`
- `tools/vex_ref/extract_fixture.py` only for already-supported VEX patterns
- `tools/vex_ref/fixtures/*`
- `Instances/Examples/*`
- `Instances.lean`

## Must Not Touch
- `Instances/ISAs/*`
- `Core/*`
- `Learnability/*`
- JSON schema
- bridge theorems

## Stop Immediately If
- `pyvex` emits a new VEX constructor/tag not already modeled
- flags / `cc_*` appear
- endianness changes appear
- partial-register aliasing beyond current 32-bit zero-extension appears
- `lake build` requires edits outside examples/extractor/fixtures

## Acceptance
- regenerate from pinned `angr`
- `lake build`
- no warnings
