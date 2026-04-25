# ppc_ps_hexrays

Hex-Rays plugin for IDA 9.3 that improves Wii U PowerPC paired-single decompilation.

The plugin targets instructions that IDA can disassemble but Hex-Rays often leaves as inline `__asm`, especially `psq_l`/`psq_st` stack traffic and common `ps_*` arithmetic.

It also marks Wii U paired-single callee-save prologue patterns as prologue code, including interleaved `mflr`/LR stores and `stfd` + `ps_merge10` + `stfs` saves for nonvolatile FPR paired-single lanes.

## Build

Set `IDASDK` to the IDA SDK root, either the repository root or its `src` directory, and `IDABIN` to your IDA install directory, then build with CMake and MSVC:

```cmd
cd ppc_ps_hexrays
cmake -B build -G "Visual Studio 17 2022" -A x64
cmake --build build --config Release
```

Use the matching Visual Studio generator for your installed MSVC version if it differs.

If `IDASDK` is not set, this project defaults to `../ida-sdk` from this repository.

If CMake is not on `PATH`, run the commands from a Visual Studio Developer PowerShell after installing CMake, or use the CMake executable bundled with Visual Studio.

The SDK CMake support deploys the plugin below `${IDABIN}/plugins/ppc_ps_hexrays/` when `IDABIN` points at an IDA installation. You can also copy the produced plugin directory to `%APPDATA%\Hex-Rays\IDA Pro\plugins\`.

## Current Coverage

Memory instructions are handled first because they affect stack-variable recovery:

- Unquantized displacement-based `psq_l`, `psq_st` with `W=0, I=0` are emitted early as two 4-byte float lane loads/stores, improving Hex-Rays variable recognition before lvar allocation.
- Non-displacement or quantized `psq_l`, `psq_st` forms still use explicit helpers, avoiding unsafe reinterpretation when exact lane memory semantics are not emitted.
- Other `psq_*` forms are converted to explicit helper calls so they no longer appear as raw inline assembly.

Function prologue handling covers Wii U paired-single save sequences:

- `stfd fN, slot(r1)` + `ps_merge10 fN, fN, fN` + `stfs fN, slot+8(r1)` is treated as a callee-save sequence rather than body code.
- Delayed `mflr rX` + `stw rX, sender_lr(r1)` inside the same save block is marked as prologue so Hex-Rays does not attach the LR save to the first real branch/body block.

Common lane-wise paired-single operations are lowered early to scalar float microcode where possible:

- `ps_add`, `ps_sub`, `ps_mul`, `ps_div`
- `ps_muls0`, `ps_muls1`
- `ps_neg`, `ps_mr`
- `ps_merge00`, `ps_merge01`, `ps_merge10`, `ps_merge11`

Remaining paired-single operations are converted to typed helper calls:

- `ps_madd`, `ps_msub`, `ps_nmadd`, `ps_nmsub`
- `ps_madds0`, `ps_madds1`
- `ps_abs`, `ps_nabs`
- vector sum helpers `ps_sum0`, `ps_sum1`
- reciprocal estimate helpers `ps_res`, `ps_rsqrte`
- compare helpers `ps_cmpu0`, `ps_cmpu1`, `ps_cmpo0`, `ps_cmpo1`

The scalar lane lowering lets the decompiler's normal optimizer delete unused lanes and recover ordinary float locals before final pseudocode is built. The helper calls preserve register dataflow for operations that are not yet lowered without pretending paired-single vectors are scalar doubles.

The plugin installs a named `ppc_ps_t` typedef for paired-single values. This keeps helper signatures and propagated casts shorter than Hex-Rays' anonymous `struct { float ps0; float ps1; }` fallback, especially for expressions that reinterpret adjacent `float` fields as one paired-single value.

Simple paired-single helper assignments to adjacent float fields are simplified back into lane-wise float operations when all inputs are unquantized `psq_l` values or other supported paired-single helpers. This currently covers `ps_add`, `ps_sub`, `ps_mul`, `ps_div`, `ps_muls0`, `ps_muls1`, `ps_neg`, `ps_mr`, and the `ps_merge*` family, so patterns like storing `__ppc_ps_add(__ppc_psq_l(&a, 0, 0), __ppc_psq_l(&b, 0, 0))` become two ordinary float assignments.

`ps_sum0`/`ps_sum1` use a scalar-use heuristic. This improves common dot-product lowering such as `ps_mul` followed by `ps_sum0`, emitting `__ppc_ps_sum0_scalar(...)` instead of leaving inline assembly or a paired-single temporary when only the scalar lane is consumed.

Scalar PowerPC floating-point select is also handled:

- `fsel` becomes `__ppc_fsel(test, ge_zero, lt_zero)`, matching PowerPC semantics: return `ge_zero` when `test >= 0`, otherwise `lt_zero`.

## Notes

The first-pass implementation intentionally only treats unquantized `psq_l/st W=0,I=0` as exact memory operations. Quantized forms require GQR-aware conversion semantics and are kept as helpers until real samples need them.
