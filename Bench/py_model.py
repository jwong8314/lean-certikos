"""Python model of the same L0 ticket-lock semantics as the Lean prototype.

This is the "Python OS" side of SCOPING.md §7, for the ticket lock:
* shared state is a log of events; `ticket` and `now` are *replay functions*
  that count events in the log (exactly `Ticket.ticket` / `Ticket.now`);
* each primitive appends one event (`FAI_t`, `get_n`, `inc_n`, `hold`);
* values are 32-bit (`n != t` is compared mod 2**32);
* scheduling: one switch point before each atomic operation, round-robin
  (the same scheduler as `Bench/Sim.lean`).

It prints the same line format as the Lean model, including an FNV-1a hash of
the log, so the two can be compared event for event (differential testing,
option D in SCOPING.md §7).

Usage: python3 py_model.py T N
"""
import sys
import time

INC_TICKET, GET_NOW, INC_NOW, HOLD = 0, 1, 2, 3
MASK = 0xFFFFFFFF


class Machine:
    def __init__(self):
        self.log = []  # oldest first

    # replay functions (O(|log|), like the Lean spec)
    def ticket(self):
        return sum(1 for (_, k) in self.log if k == INC_TICKET)

    def now(self):
        return sum(1 for (_, k) in self.log if k == INC_NOW)

    # L0 primitives: one event each
    def fai_t(self, c):
        v = self.ticket() & MASK
        self.log.append((c, INC_TICKET))
        return v

    def get_n(self, c):
        v = self.now() & MASK
        self.log.append((c, GET_NOW))
        return v

    def inc_n(self, c):
        self.log.append((c, INC_NOW))
        return 0

    def hold(self, c):
        self.log.append((c, HOLD))
        return 0


def cpu(m, c, N):
    """acq/rel client. Each `yield` is a switch point; the code between two
    yields is local work plus exactly one primitive."""
    i = 0
    while i != N:
        t = m.fai_t(c); yield            # t = FAI_t();
        n = m.get_n(c); yield            # n = get_n();
        while n != t:                    # while (n != t)
            n = m.get_n(c); yield        #   n = get_n();
        m.hold(c); yield                 # hold();
        m.inc_n(c); yield                # rel: inc_n();
        i = (i + 1) & MASK


def simulate(T, N):
    m = Machine()
    cpus = [cpu(m, c, N) for c in range(T)]
    live = [True] * T
    active, k = T, 0
    while active > 0:
        if live[k]:
            try:
                next(cpus[k])
            except StopIteration:
                live[k] = False
                active -= 1
        k = (k + 1) % T
    return m.log


def replay_ok(log, ncpu=8):
    """The protocol state machine of TicketProtocol.lean (`replay`)."""
    ticket = now = 0
    phase = {}
    for (c, k) in log:
        if c >= ncpu:
            return False
        p = phase.get(c, ("idle",))
        if k == INC_TICKET and p[0] == "idle":
            phase[c] = ("waiting", ticket); ticket += 1
        elif k == GET_NOW and p[0] == "waiting":
            pass
        elif k == HOLD and p[0] == "waiting" and p[1] == now:
            phase[c] = ("holding", p[1])
        elif k == INC_NOW and p[0] == "holding":
            phase[c] = ("idle",); now += 1
        else:
            return False
        if sum(1 for q in phase.values() if q[0] == "holding") > 1:
            return False
    return True


def fnv(log):
    h = 14695981039346656037
    for (c, k) in log:
        for ch in f"{c}:{k};":
            h = ((h ^ ord(ch)) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return h


if __name__ == "__main__":
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    t0 = time.perf_counter_ns()
    log = simulate(T, N)
    t1 = time.perf_counter_ns()
    ok = "true" if replay_ok(log) else "false"
    print(f"py-model {T} {N} {len(log)} {fnv(log)} {ok} {(t1 - t0) / 1e6}")
