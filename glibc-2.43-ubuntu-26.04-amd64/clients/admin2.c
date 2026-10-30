/* A variant of the admin program (`admin.c`: a name buffer and a `volatile` "admin" flag from `malloc`, the name
   read with one `read` of up to 32 bytes): if the bytes read contain a newline, an error line on standard error and exit status 3; otherwise
   as admin, with the writes split otherwise: "Hello, ", the name and "!\n", then the flag's line "admin: no\n" (or
   "admin: yes\n") on a line of its own.

   Exit status 0 when the lines are written, 1 when the `read` fails or a `write` fails or writes fewer bytes than
   asked, 2 when a `malloc` returns a null pointer, 3 for a name with a newline. The newline search is a loop of
   `main`'s own, not `memchr`. The flag is `volatile` as in admin (otherwise gcc deletes its store and its test). */
#include <stdlib.h>
#include <unistd.h>

#define NAME_SIZE 32

int main(void) {
  char *name = malloc(NAME_SIZE);
  volatile char *admin = malloc(1);
  if (name == NULL || admin == NULL) return 2;
  *admin = 0;
  ssize_t n = read(0, name, NAME_SIZE);
  if (n < 0) return 1;
  for (ssize_t i = 0; i < n; i++) {
    if (name[i] == '\n') {
      write(2, "admin2: bad name\n", 17);
      return 3;
    }
  }
  if (write(1, "Hello, ", 7) != 7) return 1;
  if (write(1, name, n) != n) return 1;
  if (write(1, "!\n", 2) != 2) return 1;
  if (*admin) {
    if (write(1, "admin: yes\n", 11) != 11) return 1;
  } else {
    if (write(1, "admin: no\n", 10) != 10) return 1;
  }
  return 0;
}
