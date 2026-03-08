# Opcode Backfill Lane: Branch Slice

## Scope

Expand only within the already-supported branch slice.

Good targets:
- more `jrcxz` patterns
- supported linear tails after `jrcxz`
- combinations with current no-flags width-safe blocks

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
- branch semantics implementation

## Stop Immediately If
- a fixture needs a new branch constructor
- a fixture needs multiple exits beyond current shape
- a fixture needs flags / condition-code semantics
- `lake build` requires edits outside examples/extractor/fixtures

## Acceptance
- regenerate from pinned `angr`
- `lake build`
- no warnings
