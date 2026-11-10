"""Run every benchmark and write bench/results.csv and bench/RESULTS.md.

Two benchmarks:

1. Native lock latency (OSDI'16 §6 methodology): T threads, empty critical
   section, one lock, ns per acquire+release ("transaction").
     certikos-c      CertiKOS ticket lock, transcribed from OSDI'16 Fig. 7
     ours-c          C printed from our verified ClightL ASTs, SC atomics
     ours-c-acqrel   same C, acquire/release primitives
     python-threads  same algorithm in CPython with threads
2. Executable model: T CPUs x N transactions on the log semantics, with
   CertiKOS's "one switch point before each atomic operation", round-robin.
     lean-model      Lean: verified ASTs run by ClightL.step (compiled binary)
     py-model        Python model of the same semantics
   The two must produce the same log; this is checked (FNV hash + length).

Usage: python3 run_all.py [--quick]
"""
import csv
import os
import platform
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
QUICK = "--quick" in sys.argv


def sh(args, timeout=900):
    return subprocess.run(args, capture_output=True, text=True, timeout=timeout, check=True).stdout.strip()


def build():
    lean_bin = os.path.join(ROOT, ".tools", "lean-4.35.0-darwin_aarch64", "bin")
    env = dict(os.environ, PATH=lean_bin + ":" + os.environ["PATH"])
    subprocess.run(["lake", "build", "sim", "emitc"], cwd=ROOT, env=env, check=True,
                   capture_output=True)
    os.makedirs(os.path.join(HERE, "gen"), exist_ok=True)
    os.makedirs(os.path.join(HERE, "bin"), exist_ok=True)
    with open(os.path.join(HERE, "gen", "ours_ticket.h"), "w") as f:
        f.write(sh([os.path.join(ROOT, ".lake", "build", "bin", "emitc")]) + "\n")
    cc = ["clang", "-O2", "-std=c11", "-Wall", "-I" + HERE, os.path.join(HERE, "lockbench.c"), "-lpthread"]
    sh(cc + ["-DIMPL_CERTIKOS", "-o", os.path.join(HERE, "bin", "lb_certikos")])
    sh(cc + ["-DIMPL_OURS", "-o", os.path.join(HERE, "bin", "lb_ours")])
    sh(cc + ["-DIMPL_OURS", "-DOURS_RA", "-o", os.path.join(HERE, "bin", "lb_ours_ra")])


def native(rows):
    threads = [1, 2, 4] if QUICK else [1, 2, 4, 6, 8]
    for t in threads:
        n = (200000 if QUICK else 2000000) if t == 1 else (50000 if QUICK else 300000)
        for b in ["lb_certikos", "lb_ours", "lb_ours_ra"]:
            impl, th, ns, exp, got = sh([os.path.join(HERE, "bin", b), str(t), str(n), "5"]).split(",")
            rows.append(dict(bench="native", impl=impl, T=th, N=n, ns_per_txn=ns,
                             check="ok" if exp == got else f"FAIL {got}/{exp}"))
            print(rows[-1], flush=True)
        secs = "0.5" if QUICK else "2"
        impl, th, ns, exp, got = sh([sys.executable, "-I", os.path.join(HERE, "py_threads.py"),
                                     str(t), secs, "3"]).split(",")
        rows.append(dict(bench="native", impl=impl, T=th, N=f"{secs}s", ns_per_txn=ns,
                         check="ok" if exp == got else f"FAIL {got}/{exp}"))
        print(rows[-1], flush=True)


def model(rows):
    configs = [(1, 100), (2, 50), (4, 25), (4, 50)] if QUICK else \
        [(1, 200), (2, 100), (4, 50), (4, 100), (8, 25), (8, 50)]
    sim = os.path.join(ROOT, ".lake", "build", "bin", "sim")
    for (t, n) in configs:
        outs = {}
        for name, cmd in [("lean-model", [sim, str(t), str(n)]),
                          ("py-model", [sys.executable, "-I", os.path.join(HERE, "py_model.py"), str(t), str(n)])]:
            runs = [sh(cmd).split() for _ in range(3)]
            ms = statistics.median(float(r[6]) for r in runs)
            outs[name] = runs[0]
            rows.append(dict(bench="model", impl=name, T=t, N=n, log_len=runs[0][3],
                             ms=f"{ms:.2f}", replay_ok=runs[0][5]))
        same = outs["lean-model"][3:5] == outs["py-model"][3:5]
        for r in rows[-2:]:
            r["logs_equal"] = "yes" if same else "NO"
            r["us_per_event"] = f"{1000 * float(r['ms']) / int(r['log_len']):.2f}"
        print(rows[-2], rows[-1], flush=True)


def write(rows):
    keys = ["bench", "impl", "T", "N", "ns_per_txn", "check", "log_len", "ms", "us_per_event",
            "replay_ok", "logs_equal"]
    with open(os.path.join(HERE, "results.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in keys})

    nat = [r for r in rows if r["bench"] == "native"]
    impls = ["certikos-c", "ours-c", "ours-c-acqrel", "python-threads"]
    ts = sorted({int(r["T"]) for r in nat})
    get = {(r["impl"], int(r["T"])): r for r in nat}
    lines = ["# Benchmark results", "",
             f"Machine: {platform.machine()} {platform.platform()}, "
             f"{os.cpu_count()} logical CPUs; clang -O2; Python {platform.python_version()}.", "",
             "## 1. Native lock latency (ns per acquire+release, empty critical section, median of rounds)", "",
             "| threads | " + " | ".join(impls) + " |", "|---|" + "---|" * len(impls)]
    for t in ts:
        cells = []
        for i in impls:
            r = get.get((i, t))
            cells.append("—" if r is None else r["ns_per_txn"] + ("" if r["check"] == "ok" else " ⚠"))
        lines.append(f"| {t} | " + " | ".join(cells) + " |")
    lines += ["", "Efficiency `T·t(1) / t(T)` as in OSDI'16 Fig. 11 (1.0 = scales perfectly for a single lock):", "",
              "| threads | " + " | ".join(impls) + " |", "|---|" + "---|" * len(impls)]
    for t in ts:
        cells = []
        for i in impls:
            r, r1 = get.get((i, t)), get.get((i, 1))
            cells.append("—" if not r or not r1 else f"{1 * float(r1['ns_per_txn']) * t / float(r['ns_per_txn']):.2f}")
        lines.append(f"| {t} | " + " | ".join(cells) + " |")
    bad = [r for r in nat if r["check"] != "ok"]
    lines += ["", "Mutual-exclusion check (shared counter incremented under the lock): " +
              ("all runs exact." if not bad else "FAILURES: " + "; ".join(f"{r['impl']} T={r['T']} {r['check']}" for r in bad)),
              "", "## 2. Executable model (log semantics, one switch point per atomic operation, round-robin)", "",
              "| CPUs × txns | log events | lean-model ms | py-model ms | lean µs/event | py µs/event | logs identical | replay ok |",
              "|---|---|---|---|---|---|---|---|"]
    mod = [r for r in rows if r["bench"] == "model"]
    for k in range(0, len(mod), 2):
        a, b = mod[k], mod[k + 1]
        lines.append(f"| {a['T']} × {a['N']} | {a['log_len']} | {a['ms']} | {b['ms']} | {a['us_per_event']} | "
                     f"{b['us_per_event']} | {a['logs_equal']} | {a['replay_ok']}/{b['replay_ok']} |")
    lines += ["", "The CertiKOS Coq model cannot be run here: the mC2/CCAL sources are not public, "
              "and the artifact's OCaml extraction is not available.", ""]
    with open(os.path.join(HERE, "RESULTS.md"), "w") as f:
        f.write("\n".join(lines))


if __name__ == "__main__":
    build()
    rows = []
    native(rows)
    model(rows)
    write(rows)
    print(open(os.path.join(HERE, "RESULTS.md")).read())
