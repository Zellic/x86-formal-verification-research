/* The admin program: a name buffer and an "admin" flag from `malloc`, the name read from standard input with a
   bounded length, one line with the name and the flag written to standard output. With READ_LEN = NAME_SIZE, as
   `build.sh` builds it, no input can set the flag; built without fortification and with READ_LEN past the name buffer
   (`-U_FORTIFY_SOURCE -DREAD_LEN=64`), a long name would overwrite it.

   Exit status 0 when the line is written, 1 when the `read` fails or a `write` fails or writes fewer bytes than asked,
   2 when a `malloc` returns a null pointer. The flag is `volatile`: otherwise gcc knows that `read` cannot reach a
   fresh `malloc` block and deletes both the flag's store and its test. */
#include <stdlib.h>
#include <unistd.h>

#define NAME_SIZE 32
#ifndef READ_LEN
#define READ_LEN NAME_SIZE
#endif

int main(void) {
  char *name = malloc(NAME_SIZE);
  volatile char *admin = malloc(1);
  if (name == NULL || admin == NULL) return 2;
  *admin = 0;
  ssize_t n = read(0, name, READ_LEN);
  if (n < 0) return 1;
  if (write(1, "Hello, ", 7) != 7) return 1;
  if (write(1, name, n) != n) return 1;
  if (*admin) {
    if (write(1, "! admin: yes\n", 13) != 13) return 1;
  } else {
    if (write(1, "! admin: no\n", 12) != 12) return 1;
  }
  return 0;
}
