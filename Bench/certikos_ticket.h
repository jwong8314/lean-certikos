/* CertiKOS (mC2) ticket lock, transcribed from OSDI'16 "CertiKOS: An Extensible
 * Architecture for Building Certified Concurrent OS Kernels", Figure 7.
 * The mC2 sources are not public (available on request only), so this is the
 * paper's code, not the verified binary.
 *
 *   typedef struct { volatile uint ticket; volatile uint now; } ticket_lock;
 *   ticket_lock L[NUM_LOCK];
 *   void acq_lock(uint i) { uint t; t = FAI(&L[i].ticket); while (L[i].now != t) {} pull(i); }
 *   void rel_lock(uint i) { push(i); L[i].now++; }
 *
 * FAI is x86 `lock xaddl`; here it is __sync_fetch_and_add (a full barrier;
 * `ldaddal` on arm64). `pull`/`push` copy the lock-protected shared memory in
 * mC2; the benchmark has no protected data, so they are empty, as `hold` is.
 * `now` is a plain volatile access, as in the paper: correct under x86-TSO,
 * which CertiKOS assumes (it models shared primitives as sequentially
 * consistent). On arm64 the release store is not ordered after the critical
 * section; the harness's check mode reports what happens.
 */
#include <stdint.h>
#define NUM_LOCK 8
typedef unsigned int uint;
typedef struct { volatile uint ticket; volatile uint now; } ticket_lock;
static ticket_lock L[NUM_LOCK];

static inline uint FAI(volatile uint *p) { return __sync_fetch_and_add(p, 1u); }
static inline void pull(uint i) { (void)i; }
static inline void push(uint i) { (void)i; }

static inline void acq_lock(uint i) {
  uint t;
  t = FAI(&L[i].ticket);
  while (L[i].now != t) {}
  pull(i);
}

static inline void rel_lock(uint i) {
  push(i);
  L[i].now++;
}
