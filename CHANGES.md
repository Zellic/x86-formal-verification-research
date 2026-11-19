# Changes

## Release 2

- **glibc's `memrchr`**: seven theorems about the four x86-64 variants as Ubuntu 26.04's `libc.a` ships them, two of
  them rebuilt with a fix, and the proof that `__memrchr_evex` does not implement `memrchr` for objects of `2^32` bytes
  or more (`glibc-2.43-ubuntu-26.04-amd64/Glibc243Ubuntu/MemrchrStatement.lean`). `libc.a` is not in the repository:
  `get-libc.sh` downloads Ubuntu's package and checks its hash.
- **The first release's theorems again, with new proofs** (`memcmp`'s five builds, admin, admin2). Their statements
  say what they said, with these changes in the vocabulary and the model:
  - admin's and admin2's launches (`DemoArgs`) have the soft `RLIMIT_AS` and `RLIMIT_DATA` unlimited, as glibc's
    allocator's proofs assume at every call (admin's `DemoLimits` is then implied).
  - a contract says how much stack the function uses (`Contract.stack`), and that a call's data lies apart from the
    function's frame is stated once, by `CallOf` (`CallOf.frameApart`), instead of in each contract's precondition.
    For `memcmp` it is the same condition as before: neither string overlaps the return address's slot.
  - `Profile.Consistent` has one more condition: a processor whose `CPUID` reports `XSAVEC` with `XSAVE` enabled has
    the feature (the model now executes `XSAVEC`).
  - the model executes more instructions (`MODEL-LIMITATIONS.md`).
- **One Lean version**: Lean 4.35 builds the statements, exports the proofs and checks them; the first release used
  4.34 for the statements and exports. The exports are new files, under `…/x86fv/proofs/release-2/`.

## Release 1

- `memcmp` compiled by GCC 15 (`-O1`, `-O2`, `-Os`) and Clang 21 (`-O2`, `-Os`): each build implements C's `memcmp`.
- admin and admin2, two small C programs statically linked against glibc 2.43: under the stated hypotheses, neither
  ever reports an admin.
