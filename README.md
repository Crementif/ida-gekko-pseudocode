# IDA Gekko Pseudocode Extension
**IDA Pro plugin for improving paired-single pseudocode decompilation on PowerPC targets like the GameCube, Wii, and Wii U.**

---

## Description
This IDA plugin (currently targetting IDA 9.3) makes various improvements to the paired single floating point instructions support inside the decompiled pseudocode in IDA.

It currently fixes the following issues:
 - The pseudocode shows all paired single instructions using inline assembly like `__asm { psq_l f12, 0(r3), 0, 0 }` inside the pseudocode. This makes the math hard to read, partially due to it often being badly interleaved with regular floating point code.
 - `ps_merge*` instructions are also used in the pseudocode function prologues, which causes the stack setup to end abruptly and become part of the function body which leads to further degradation of the decompilation quality.

Both of these issues made it harder than necessary to look through floating point heavy code in GameCube, Wii and Wii U games.  
That is what led me to creating this plugin, albeit with a healthy dose of AI coding. So use it or don't if the latter isn't your thing.

## Preview

I wanted to make the SIMD code look as close as possible to the regular floating point code, and not emit a lot of Gekko-specific intrinsics if possible.  
There's a fallback to intrinsics for more complex operations.

| Before | After |
|---|---|
| ![Before small](images/before_small.png) | ![After small](images/after_small.png) |
| ![Before big](images/before_big.png) | ![After big](images/after_big.png) |

## Install

The release builds of this plugin are compiled with the IDA 9.3 SP1 SDK.
For older/newer IDA versions, you will likely have to build from source with the appropriate IDA SDK version.

To install from GitHub releases:

1. Download the latest release from `https://github.com/Crementif/ida-gekko-pseudocode/releases`.
2. Extract the release archive.
3. Copy the included `ida_gekko_pseudocode` plugin directory into your IDA plugins directory.
4. Restart IDA if it was already running.

Typical plugin locations are:

- `%APPDATA%\Hex-Rays\IDA Pro\plugins\`
- `<IDA install dir>\plugins\`

Now, whenever you decompile a function that contains paired-single instructions, the plugin will automatically apply its improvements to the pseudocode output.
It doesn't retroactively change existing pseudocode, so you might have to press `F5` again in already-open pseudocode views to see the changes.

Sometimes, you might want to see the original pseudocode for a project (temporarily).
You can disable it on a per-database basis (or temporarily disable it before pressing `F5`) by right-clicking in the pseudocode view and then toggling the "Always Fix Paired Singles In Functions" option in the context menu.
From now on, the plugin should have no effects when you decompile functions in that database, until you re-enable the option.

You might have to go to `Edit`->`Other`->`Reset decompiler information` to clear out any changes that the plugin made.
Make sure to not toggle any aggressive options here. I think the microcode option is really the only one necessary.

## Build

Set `IDASDK` to the IDA SDK root, either the repository root or its `src` directory, and `IDABIN` to your IDA install directory, then build with CMake and MSVC:

```cmd
cmake -B build -G "Visual Studio 17 2022" -A x64
cmake --build build --config Release
```

Use the matching Visual Studio generator for your installed MSVC version if it differs.

If `IDASDK` is not set, this project defaults to the in-repo `ida-sdk` submodule. If you cloned without submodules, run `git submodule update --init --recursive` first.

If CMake is not on `PATH`, run the commands from a Visual Studio Developer PowerShell after installing CMake, or use the CMake executable bundled with Visual Studio.

The SDK CMake support deploys the plugin below `${IDABIN}/plugins/` when `IDABIN` points at an IDA installation. You can also copy the produced plugin directory to `%APPDATA%\Hex-Rays\IDA Pro\plugins\`.

## Current Coverage

Coverage is focused on the Wii U paired-single patterns that most affect decompilation quality.

- Exact displacement `psq_l` and `psq_st` forms are lowered early during microcode generation when `I=0`.
- `W=0` is emitted as two 32-bit float lane loads/stores, and `W=1` is emitted as a lane-0 float transfer plus the architectural lane-1 `1.0f` value.
- This early lowering happens before lvar allocation, which improves stack-variable recovery and lets Hex-Rays optimize away unused lanes like normal scalar float code.
- Quantized forms and non-displacement or indexed `psq_*` variants are not reinterpreted as exact memory traffic. They stay as typed helpers such as `__ppc_psq_l`, `__ppc_psq_st`, `__ppc_psq_lx`, or `__ppc_psq_stux` until there is enough reason to model their full GQR-dependent semantics.

- Wii U paired-single callee-save prologues are recognized and marked as prologue code.
- This includes `stfd fN, slot(r1)` + `ps_merge10 fN, fN, fN` + `stfs fN, slot+8(r1)` save sequences, as well as delayed `mflr rX` + `stw rX, sender_lr(r1)` patterns that belong to the same save block.
- Marking these as prologue keeps Hex-Rays from attaching save/setup instructions to the first real body block.

- The plugin lowers many common paired-single operations directly to lane-wise float microcode or per-lane scalar helpers: `ps_add`, `ps_sub`, `ps_mul`, `ps_div`, `ps_muls0`, `ps_muls1`, `ps_madd`, `ps_msub`, `ps_nmadd`, `ps_nmsub`, `ps_madds0`, `ps_madds1`, `ps_neg`, `ps_abs`, `ps_nabs`, `ps_mr`, `ps_merge00`, `ps_merge01`, `ps_merge10`, `ps_merge11`, `ps_sum0`, `ps_sum1`, `ps_res`, `ps_rsqrte`, and `ps_sel`.
- `ps_sum0` and `ps_sum1` are handled early, with an older scalar-use heuristic still available as a fallback when direct emission is not possible.
- Scalar PowerPC `fsel` is also handled and emitted as `__ppc_fsel(test, ge_zero, lt_zero)` with the expected PowerPC `test >= 0 ? ge_zero : lt_zero` behavior.

- Compare operations `ps_cmpu0`, `ps_cmpu1`, `ps_cmpo0`, and `ps_cmpo1` are emitted as typed helpers.
- Any paired-single operation that is recognized but not safely lowered still becomes a typed helper call instead of raw inline assembly, which preserves dataflow without pretending paired-single values are scalar doubles.

- The plugin installs a named `ppc_ps_t` typedef so helper signatures and propagated casts stay readable.
- A final ctree cleanup can rewrite simple whole-pair helper assignments back into adjacent float-lane expressions, including common `ps_madd`/`ps_msub` families and `psq_l(..., 1, 0)` lane materialization, so surviving helper-based output still decompiles more cleanly.
