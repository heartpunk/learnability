# VEX Reference Plan

## Pins

- Packaging flake: `github:heartpunk/angr-nix/2f20f9ed68506bd151ed171e505942ac9a2a0b43`
- Upstream `angr`: `v9.2.204` (`359a018f01e27b6d4a8e872d08f4f17c0a092441`)
- Upstream `pyvex`: `v9.2.204` (`623dbb9c40df8eed7d514c6767d86afd315a5b4e`)

## Initial Scope

- Architecture: AMD64
- IR: VEX IRSB
- Fragment: straight-line basic blocks
- No memory side effects
- No flags
- No calls, syscalls, dirty helpers, or exceptions
- Only boring fallthrough exits

## First End-to-End Fixture

- Bytes: `48 8d 47 05`
- Instruction: `lea rax, [rdi+0x5]`
- Base address: `0x400000`
- Concrete input: `rdi = 0x10`
- Expected output: `rax = 0x15`, `rip = 0x400004`

## Reference Workflow

Everything Python-side runs inside the nix shell.

```sh
nix develop . --fallback -c sh -lc '
  cd tools/vex_ref
  uv venv --clear --python "$(command -v python)" --system-site-packages .venv
  . .venv/bin/activate
  uv run --active extract_fixture.py \
    --name amd64_lea_rdi_plus_5 \
    --arch amd64 \
    --base 0x400000 \
    --bytes 488d4705 \
    --input-reg rdi=0x10
'
```

Outputs:

- JSON fixture: `tools/vex_ref/fixtures/amd64_lea_rdi_plus_5.json`
- Lean fixture: `Instances/Examples/VexLeaRdiPlus5Fixture.lean`
