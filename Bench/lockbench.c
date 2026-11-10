/* Lock latency benchmark, following the methodology of OSDI'16 §6
 * ("we put an empty critical section under the protection of a single lock").
 *
 * Usage: lockbench <threads> <transactions per thread> <rounds>
 * Prints one CSV line per run:
 *   impl,threads,ns_per_txn_median,check_expected,check_got
 *
 * Check mode: a separate run increments a plain shared counter inside the
 * critical section; a correct lock gives exactly threads*N. */
#define _GNU_SOURCE
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

#if defined(IMPL_CERTIKOS)
#include "certikos_ticket.h"
#define ACQ() acq_lock(0)
#define REL() rel_lock(0)
#define IMPL "certikos-c"
#elif defined(IMPL_OURS)
#include "ours_prims.h"
#include "gen/ours_ticket.h"
#define ACQ() ours_acq()
#define REL() ours_rel()
#ifdef OURS_RA
#define IMPL "ours-c-acqrel"
#else
#define IMPL "ours-c"
#endif
#else
#error "define IMPL_CERTIKOS or IMPL_OURS"
#endif

static volatile long counter;
static long N;
static int check;
static volatile int ready, go;

static void *worker(void *arg) {
  (void)arg;
  __atomic_fetch_add(&ready, 1, __ATOMIC_SEQ_CST);
  while (!__atomic_load_n(&go, __ATOMIC_ACQUIRE)) {}
  if (check) {
    for (long i = 0; i < N; i++) { ACQ(); counter = counter + 1; REL(); }
  } else {
    for (long i = 0; i < N; i++) { ACQ(); REL(); }
  }
  return NULL;
}

static double run(int threads) {
  pthread_t th[64];
  ready = 0; go = 0;
  for (int i = 0; i < threads; i++) pthread_create(&th[i], NULL, worker, NULL);
  while (__atomic_load_n(&ready, __ATOMIC_SEQ_CST) < threads) {}
  struct timespec a, b;
  clock_gettime(CLOCK_MONOTONIC, &a);
  __atomic_store_n(&go, 1, __ATOMIC_RELEASE);
  for (int i = 0; i < threads; i++) pthread_join(th[i], NULL);
  clock_gettime(CLOCK_MONOTONIC, &b);
  double ns = (b.tv_sec - a.tv_sec) * 1e9 + (b.tv_nsec - a.tv_nsec);
  return ns / ((double)threads * (double)N);
}

static int cmp(const void *x, const void *y) {
  double a = *(const double *)x, b = *(const double *)y;
  return (a > b) - (a < b);
}

int main(int argc, char **argv) {
  int threads = argc > 1 ? atoi(argv[1]) : 1;
  long n = argc > 2 ? atol(argv[2]) : 1000000;
  int rounds = argc > 3 ? atoi(argv[3]) : 5;
  if (threads < 1 || threads > 64 || rounds < 1 || rounds > 101) return 2;

  /* check run */
  check = 1; N = n; counter = 0;
  run(threads);
  long got = counter;

  /* timing runs (empty critical section) */
  check = 0;
  double t[101];
  run(threads); /* warm-up */
  for (int r = 0; r < rounds; r++) t[r] = run(threads);
  qsort(t, rounds, sizeof t[0], cmp);
  printf("%s,%d,%.2f,%ld,%ld\n", IMPL, threads, t[rounds / 2], (long)threads * n, got);
  return 0;
}
