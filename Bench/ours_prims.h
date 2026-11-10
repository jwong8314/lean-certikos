/* L0 primitives for the C printed from our verified ClightL ASTs.
 * Our L0 layer (Ticket.prims) makes each primitive one atomic, sequentially
 * consistent event, so each is implemented as one SC atomic operation. */
#include <stdint.h>
typedef struct { volatile uint32_t ticket; volatile uint32_t now; } ours_lock_t;
static ours_lock_t ours_lock;

#ifndef OURS_RA
/* Default: every primitive is a sequentially consistent atomic (the L0 model). */
static inline uint32_t FAI_t(void) { return __atomic_fetch_add(&ours_lock.ticket, 1u, __ATOMIC_SEQ_CST); }
static inline uint32_t get_n(void) { return __atomic_load_n(&ours_lock.now, __ATOMIC_SEQ_CST); }
static inline uint32_t inc_n(void) { __atomic_fetch_add(&ours_lock.now, 1u, __ATOMIC_SEQ_CST); return 0u; }
#else
/* Minimal ordering: acquire on entry, release on exit. `inc_n` may be a plain
 * load + release store because only the lock holder ever writes `now`
 * (theorem `Ticket.mutex`). Not covered by the SC proof (SCOPING.md §5). */
static inline uint32_t FAI_t(void) { return __atomic_fetch_add(&ours_lock.ticket, 1u, __ATOMIC_RELAXED); }
static inline uint32_t get_n(void) { return __atomic_load_n(&ours_lock.now, __ATOMIC_ACQUIRE); }
static inline uint32_t inc_n(void) {
  __atomic_store_n(&ours_lock.now, __atomic_load_n(&ours_lock.now, __ATOMIC_RELAXED) + 1u, __ATOMIC_RELEASE);
  return 0u;
}
#endif
static inline uint32_t hold(void)  { return 0u; }
