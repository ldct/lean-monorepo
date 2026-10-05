# Module declaration experiment — 2026-09-11

Tested Scratch through LSP with identical on-disk file URI and unsaved text, either
unchanged or prefixed with `module\n`. No playground source was converted.
Adjusted goal position for the extra line. Every run asserted no errors and the
same goal. Fresh server per run, first opening of each variant excluded as warmup,
then three alternating runs per variant. No GUI rendering measurement.

## Current optimized project

| Median | Legacy header | module header |
| --- | ---: | ---: |
| Open to checked | 3.188 s | 4.312 s |
| Initialization through goal | 4.047 s | 5.148 s |

The module variant was 1.124 s (35%) slower in this current configuration. All
measured requests hit the setup cache, which still has no filesystem validation.
This is not a claim that module imports are inherently slower: optimized lazy
private/IR loading only applies to legacy roots. A separate CLI diagnostic of the
module variant confirmed its tactic-image key is different and absent
(exts-15691199144094516847), whereas the legacy image exists. Thus this compares
what is installed today, not equally tuned image caches for both modes.

Raw results: playground/.lake/infoview-investigation/module-comparison.json.
Probe: playground/.lake/infoview-investigation/probe-module.py.

The declaration opts into Lean's public/private module system. It can avoid
loading private dependency details, changes default declaration/import visibility,
and overlaps the existing lazy-parts optimization. Snapshots also overlap by
restoring an environment, and must be regenerated for changed headers.

## Stock 4.33.1 project

Same LSP comparison in ../v4.33.1/playground, using stock runtime and its own
package artifact paths, with no custom setup cache. First legacy opening was
35.947 s cold and is excluded; module warmup was 9.344 s and is also excluded.

| Median of three warm runs | Legacy | module |
| --- | ---: | ---: |
| Open to checked | 8.690 s | 8.200 s |
| Initialization through goal | 9.512 s | 9.016 s |

Module saves about 0.490 s (5.6%) of stock editor opening time here. It does not
avoid Lake setup. All proof/goal checks passed. No source conversion was made.
Raw data: ../v4.33.1/playground/.lake/infoview-investigation/module-comparison.json.

## Stock editor memory

Two alternating runs per mode, fresh server, all Scratch proofs/goals validated.
Sampled process-tree RSS via ps every approximately 100 ms and immediately after
the goal response. The file worker (largest Lean child) held 5.713 GB
without module versus 3.305 GB with module (decimal GB): approximately
42% less resident memory, a 2.41 GB reduction. Worker observations were stable:
legacy 5,580,944 / 5,577,152 KiB; module 3,227,088 / 3,228,016 KiB.

Summed server-tree RSS was approximately 7.14 GB vs 4.68 GB, but summing RSS can
double-count shared pages, so use file-worker RSS for the primary comparison.
RSS is not Activity Monitor physical footprint or whole-VS-Code memory. Sampling
can miss brief peaks; observed tree peaks equaled the after-goal observations.
Raw data: ../v4.33.1/playground/.lake/infoview-investigation/module-memory.json.
