import ZellicX86.Load.FileImage
/-!
# The build's static archive

`libc.a` (a copy of Ubuntu 26.04's `libc6-dev` 2.43-2ubuntu2.4 `/usr/lib/x86_64-linux-gnu/libc.a`) as `LibcA.blob`,
by the trusted loader `#file_image` (`ZellicX86/Load/FileImage.lean`): the file with this SHA-256, read when this module
is built. What the statements about its objects mean rests on this line.
-/
namespace Glibc243Ubuntu

#file_image "../libc.a" sha256 "2a277b999268f100c5f838689704b7432e9b1fdac76bf0cbda83cdbbaecc89e2" as LibcA

end Glibc243Ubuntu
