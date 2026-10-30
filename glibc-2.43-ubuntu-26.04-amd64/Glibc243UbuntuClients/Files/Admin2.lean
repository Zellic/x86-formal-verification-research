import ZellicX86.Load.FileImage
/-!
# The file of the client program `admin2`

`clients/admin2` (`clients/admin2.c`, built by `clients/build.sh`) as `Clients.Admin2.file`, by the
trusted loader `#file_image` (`ZellicX86/Load/FileImage.lean`): the file with this SHA-256, read when this module is built. A statement about `admin2`
takes its executable bytes and ELF metadata from this exact file image.
-/

#file_image "../../clients/admin2" sha256 "7e51ba5891e4438f2c414cfe20d6fc2471d0afd25aeff71422afc1847a16b08a"
  as Clients.Admin2.file
