import ZellicX86.Load.FileImage
/-!
# `memrchr`'s variants with their bugs fixed, as object files

glibc 2.43's `memrchr-evex.S` and `memrchr-avx2.S`, each with its fix (`fixed/memrchr-evex.patch`: the page-crossing
path's length computed in 64 bits; `fixed/memrchr-avx2.patch`: a `jb` to the null return after each subtraction that can
borrow), assembled as glibc's build of `libc.a` assembles them (`fixed/build.sh`, which also checks that the unpatched
builds give the bytes of `libc.a`): the files in `fixed/`,
by the framework's trusted loader `#file_image`, each the file with this SHA-256, read when this module is built. What
the statements about the fixed functions mean rests on these lines, as those about `libc.a` rest on `LibcA.lean`'s.
-/
namespace Glibc243Ubuntu

#file_image "../fixed/memrchr-evex-fixed.o" sha256 "2f3c3767a8dbbabf0a744efed86d5a7c116aa571da300abef43a9511135916d9" as MemrchrEvexFixedO

#file_image "../fixed/memrchr-avx2-fixed.o" sha256 "917326ca79a105c7fa98edfe141dd6cf55a1191353d5ab23b133d7cf262e2207" as MemrchrAvx2FixedO

end Glibc243Ubuntu
