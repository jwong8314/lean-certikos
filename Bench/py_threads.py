"""Ticket lock in Python with real threads (the same algorithm).

FAI_t is `next(itertools.count())`, which is atomic in CPython. `now` is only
written by the lock holder. Waiters spin on `now`, like the C versions.

A fixed number of transactions does not work here: with the GIL, a spinning
waiter keeps the interpreter until the 5 ms switch interval expires, so
contended hand-offs cost milliseconds. Instead each run lasts a fixed time and
counts completed transactions.

Usage: python3 py_threads.py <threads> <seconds per run> <rounds>
Prints: impl,threads,ns_per_txn_median,check_expected,check_got
(check: per-thread counts summed vs. the counter incremented under the lock)
"""
import itertools
import statistics
import sys
import threading
import time


class TicketLock:
    def __init__(self):
        self._next = itertools.count()
        self.now = 0

    def acquire(self):
        t = next(self._next) & 0xFFFFFFFF   # t = FAI_t();
        while self.now != t:                # while (get_n() != t) {}
            pass

    def release(self):
        self.now = (self.now + 1) & 0xFFFFFFFF   # inc_n();


def run(threads, seconds):
    lock = TicketLock()
    shared = [0]
    counts = [0] * threads
    stop = [False]
    start = threading.Barrier(threads + 1)

    def worker(k):
        start.wait()
        c = 0
        while not stop[0]:
            lock.acquire()
            shared[0] = shared[0] + 1
            lock.release()
            c += 1
        counts[k] = c

    ts = [threading.Thread(target=worker, args=(k,)) for k in range(threads)]
    for t in ts:
        t.start()
    t0 = time.perf_counter_ns()
    start.wait()
    time.sleep(seconds)
    stop[0] = True
    for t in ts:
        t.join()
    t1 = time.perf_counter_ns()
    total = sum(counts)
    return (t1 - t0) / max(total, 1), total, shared[0]


if __name__ == "__main__":
    threads = int(sys.argv[1]); seconds = float(sys.argv[2]); rounds = int(sys.argv[3])
    res = [run(threads, seconds) for _ in range(rounds)]
    ns = statistics.median(r[0] for r in res)
    ok_exp = sum(r[1] for r in res); ok_got = sum(r[2] for r in res)
    gil = getattr(sys, "_is_gil_enabled", lambda: True)()
    print(f"python-threads{'' if gil else '-nogil'},{threads},{ns:.2f},{ok_exp},{ok_got}")
