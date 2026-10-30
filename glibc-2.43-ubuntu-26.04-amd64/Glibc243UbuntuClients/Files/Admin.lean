import ZellicX86.Load.FileImage
/-!
# The file of the client program `admin`

`clients/admin` (`clients/admin.c`, built by `clients/build.sh`) as `Clients.Admin.file`, by the
trusted loader `#file_image` (`ZellicX86/Load/FileImage.lean`): the file with this SHA-256, read when this module is built. A statement about
`admin` takes its executable bytes and ELF metadata from this exact file image.
-/

#file_image "../../clients/admin" sha256 "72b95875992deac24bea73b4e933d628a5a1ae0f2f0fe9bc28cf9b47056d2e28"
  as Clients.Admin.file
