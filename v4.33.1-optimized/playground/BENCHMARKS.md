# Benchmark results — 2026-09-11

Apple M5 Max, 64 GiB RAM, Apple Silicon macOS. Five measured repetitions per
case/configuration after warm-up; order reverses on alternating repetitions.
Both compilers read the **same standard Mathlib v4.33.1 cache**. Mathlib was not
rebuilt and native tactics were not compiled. Values below are medians.

| Case | Stock seconds | Optimized seconds | Speedup | Switches off seconds | Peak RSS GB, stock → optimized |
| --- | ---: | ---: | ---: | ---: | ---: |
| import | 8.29 | 2.99 | 2.77× | 8.23 | 5.69 → 1.71 |
| exact | 13.51 | 5.20 | 2.60× | 11.88 | 7.91 → 2.76 |
| scratch | 10.17 | 3.48 | 2.93× | 9.07 | 5.71 → 1.75 |
| tactics | 13.54 | 7.82 | 1.73× | 12.33 | 5.83 → 1.87 |
| module | 5.37 | 3.49 | 1.54× | 3.14 | 3.28 → 1.96 |

- `import`: only `import Mathlib`.
- `exact`: import plus two `exact?` proofs; suggestions match byte for byte.
- `scratch`: the requested import-first scratch file, with `linarith`, `ring`, and `norm_num`.
- `tactics`: 100 repetitions each of `linarith`, `ring`, and `aesop` proofs (300 total).
- `module`: a `module` header, `public import Mathlib`, and a `ring` proof.

All 75 measured runs and 15 warm-up runs exited successfully with byte-identical
stdout and stderr across configurations. `lake build` also passed, compiling only
`Playground.Scratch` and `Playground`; the 8,700 pre-existing cached dependency
oleans retained their recorded sizes and modification times.

The plain-import result is 2.77× faster and uses about 70% less peak RSS. Turning
runtime optimizations off brings it back to 8.23 seconds, close to stock's 8.29.
The tactic-heavy case has nearly unchanged CPU time (8.46 → 8.11 seconds), as
expected without native tactic compilation; its wall-time gain is primarily loading.

The `module` case is a qualification: the optimized build with runtime switches
**off** is faster than with them on (3.14 versus 3.49 seconds). Thus the runtime
changes are not a universal improvement. The disabled build still uses stage 2's
rebuilt core oleans, unlike stock; this control is an ablation, not an identical
stock installation. A tactic-index image was prepared for plain `import Mathlib`,
not for every possible import/header configuration.

These measurements concern warm standalone processes. They do not establish
cold-cache performance, editor latency, or general semantic equivalence. RSS
includes shared mapped pages and should not be multiplied by the number of workers.

Reproduce from this directory:

```sh
python3 scripts/benchmark.py --repeat 5
```

See [benchmark-results.json](benchmark-results.json) for every raw timing, CPU-time,
and RSS sample, and [README.md](README.md) for the pinned sources and setup.
