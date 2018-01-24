/* TAGS: c sym */
/* VERIFY_OPTS: --symbolic --sequential -o nofail:malloc */
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assert(int);
extern unsigned int __VERIFIER_nondet_uint(void);


int main(void) {
  unsigned int x = __VERIFIER_nondet_uint();
  unsigned int y = x + 1;

  while (x < 1024) {
    x++;
    y++;
  }

  __VERIFIER_assert(x == y); /* ERROR */
}
