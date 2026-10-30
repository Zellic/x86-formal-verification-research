/* The byte comparison of the C standard (C17 7.24.4.1), written as a loop. Built as a
   freestanding object (build.sh), so the compiler neither replaces it by a call to a library
   `memcmp` nor inserts stack protection or CET markers. */
#include <stddef.h>

int memcmp(const void *a, const void *b, size_t n) {
  const unsigned char *p = a, *q = b;
  for (size_t i = 0; i < n; i++)
    if (p[i] != q[i]) return p[i] - q[i];
  return 0;
}
