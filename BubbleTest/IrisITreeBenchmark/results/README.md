# IrisITree benchmark results

## Proof size

| Layer | Files | ibubble commands | Manual Iris | Search Iris | Reduction | Generated Iris | Manual all | Search all | Reduction | Generated all |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Core | 5 | 69 | 565 | 251 | 55.6% | 1014 | 962 | 610 | 36.6% | 1512 |
| Effects | 9 | 48 | 313 | 132 | 57.8% | 545 | 514 | 308 | 40.1% | 847 |
| HeapLang | 2 | 33 | 237 | 44 | 81.4% | 245 | 324 | 112 | 65.4% | 364 |
| TOTAL | 16 | 150 | 1115 | 427 | 61.7% | 1804 | 1800 | 1030 | 42.8% | 2723 |

Iris counts Iris Proof Mode tactics, including each ibubble command. All adds ordinary Lean tactics. Reductions compare the handwritten manual variant with the search variant. Generated-script counts are reported separately because they measure persisted reconstruction code rather than handwritten proof reduction.

## Complete case-study rebuild

| Variant | Runs | Mean | Median | Min | Max |
|---|---:|---:|---:|---:|---:|
| manual | 5 | 8.502 s | 8.542 s | 8.318 s | 8.708 s |
| search | 5 | 77.675 s | 77.074 s | 76.074 s | 79.871 s |
| generated | 5 | 9.748 s | 9.676 s | 9.542 s | 10.221 s |

Each sample deletes only the selected variant's Lean artifacts and rebuilds its aggregate module. Variant order rotates between repetitions.

## Search cost per run

| Layer | Calls/run | Samples | Median/call | P90/call | P95/call | Max/call | Mean cumulative search/run |
|---|---:|---:|---:|---:|---:|---:|---:|
| Core | 100 | 500 | 0.137 s | 1.514 s | 2.837 s | 12.245 s | 57.414 s |
| Effects | 53 | 265 | 0.152 s | 1.631 s | 6.200 s | 9.431 s | 41.007 s |
| HeapLang | 76 | 380 | 0.160 s | 0.879 s | 1.249 s | 4.088 s | 29.195 s |
| TOTAL | 229 | 1145 | 0.147 s | 1.126 s | 2.647 s | 12.245 s | 127.616 s |

Calls/run counts dynamic Search.search calls; Samples covers all repetitions. The 150 textual ibubble commands expand to 229 calls per run because goal combinators may invoke a command for multiple goals. P90/call and P95/call summarize the pooled per-call samples.

Mean cumulative search/run sums calls measured with Elab.async=false; complete rebuild reports parallel wall-clock time, so these totals are not directly comparable.
