# Benchmark results

Machine: arm64 macOS-27.0.1-arm64-arm-64bit-Mach-O, 10 logical CPUs; clang -O2; Python 3.14.6.

## 1. Native lock latency (ns per acquire+release, empty critical section, median of rounds)

| threads | certikos-c | ours-c | ours-c-acqrel | python-threads |
|---|---|---|---|---|
| 1 | 3.96 | 8.03 | 4.51 | 148.10 |
| 2 | 47.48 | 53.45 | 48.13 | 22919.26 |
| 4 | 139.24 | 145.32 | 140.28 | 39023.80 |
| 6 | 163.91 | 164.65 | 164.54 | 21962.29 |
| 8 | 202.31 | 206.24 | 201.36 | 24982.23 |

Efficiency `T·t(1) / t(T)` as in OSDI'16 Fig. 11 (1.0 = scales perfectly for a single lock):

| threads | certikos-c | ours-c | ours-c-acqrel | python-threads |
|---|---|---|---|---|
| 1 | 1.00 | 1.00 | 1.00 | 1.00 |
| 2 | 0.17 | 0.30 | 0.19 | 0.01 |
| 4 | 0.11 | 0.22 | 0.13 | 0.02 |
| 6 | 0.14 | 0.29 | 0.16 | 0.04 |
| 8 | 0.16 | 0.31 | 0.18 | 0.05 |

Mutual-exclusion check (shared counter incremented under the lock): all runs exact.

## 2. Executable model (log semantics, one switch point per atomic operation, round-robin)

| CPUs × txns | log events | lean-model ms | py-model ms | lean µs/event | py µs/event | logs identical | replay ok |
|---|---|---|---|---|---|---|---|
| 1 × 200 | 800 | 1.43 | 2.53 | 1.79 | 3.16 | yes | true/true |
| 2 × 100 | 1000 | 2.48 | 4.47 | 2.48 | 4.47 | yes | true/true |
| 4 × 50 | 1792 | 10.38 | 18.81 | 5.79 | 10.50 | yes | true/true |
| 4 × 100 | 3592 | 43.65 | 74.97 | 12.15 | 20.87 | yes | true/true |
| 8 × 25 | 3352 | 44.77 | 66.22 | 13.36 | 19.76 | yes | true/true |
| 8 × 50 | 6752 | 177.86 | 270.13 | 26.34 | 40.01 | yes | true/true |

The CertiKOS Coq model cannot be run here: the mC2/CCAL sources are not public, and the artifact's OCaml extraction is not available.
