# Opcode Backfill Lane: Memory Slice

## Scope

Expand only within the already-supported memory slice.

Good targets:
- more `load64` fixtures
- more `store64` fixtures
- different supported address shapes using current expression forms
- combinations with already-supported width-safe register behavior

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
- memory semantics implementation

## Stop Immediately If
- a fixture needs width other than current `load64`/`store64`
- a fixture needs big-endian behavior
- a fixture needs new VEX load/store forms
- `lake build` requires edits outside examples/extractor/fixtures

## Acceptance
- regenerate from pinned `angr`
- `lake build`
- no warnings
