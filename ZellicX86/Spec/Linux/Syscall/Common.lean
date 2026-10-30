import ZellicX86.Spec.Linux.Stack
/-!
# Linux system calls: what every call uses

Argument and result registers, error returns, the `access_ok` check of user pointers, and the
kernel's copies to and from user memory and of path names from it. Every copy grows a stack where the
kernel's page-fault handler does for it (`growFor`).

Sources: `arch/x86/entry/syscall_64.c`, `arch/x86/include/asm/uaccess_64.h`,
`arch/x86/lib/copy_user_64.S`, `lib/strncpy_from_user.c`, `fs/namei.c` (`getname_flags`),
`include/uapi/asm-generic/errno-base.h`, `include/uapi/asm-generic/errno.h`.
-/
namespace ZellicX86

/-- `access_ok(ptr, n)` for a size not known at compile time: `ptr + n` does not wrap and is
at most `USER_PTR_MAX` (`arch/x86/include/asm/uaccess_64.h` `__access_ok`). `copy_to_user` checks
with it whatever its size: on x86 it calls the out-of-line `_copy_to_user` (`lib/usercopy.c`; x86 does
not define `INLINE_COPY_TO_USER`), where the size is a parameter, not a constant. `copy_from_user`
checks nothing on x86-64 (`copyIn`). -/
def accessOk (feat : Features) (ptr : Addr) (n : Nat) : Bool :=
  let sum := (ptr + BitVec.ofNat 64 n).toNat
  decide (sum ≤ userPtrMax feat) && decide (ptr.toNat ≤ sum)

/-- `access_ok(ptr, n)` for a size the compiler knows (`sizeof` of a structure): for at most a page
only `ptr` is checked, at most `USER_PTR_MAX` (`valid_user_address`), and the accesses that follow
decide the rest; for more, as `accessOk` (`__access_ok`). -/
def accessOkFixed (feat : Features) (ptr : Addr) (n : Nat) : Bool :=
  if n ≤ 4096 then decide (ptr.toNat ≤ userPtrMax feat) else accessOk feat ptr n

/-- `MAX_RW_COUNT` (`include/linux/fs.h`): `INT_MAX` rounded down to a page. -/
def maxRwCount : Nat := 0x7ffff000

/-- A negative error return `-e` as the kernel puts it in `rax`. -/
def errRet (e : Nat) : BitVec 64 := 0 - BitVec.ofNat 64 e

-- Error numbers several calls use; others are defined next to the calls that use them.

/-- Bad file descriptor (`include/uapi/asm-generic/errno-base.h`). -/
def EBADF : Nat := 9
/-- Bad address (`include/uapi/asm-generic/errno-base.h`). -/
def EFAULT : Nat := 14
/-- Broken pipe (`include/uapi/asm-generic/errno-base.h`). -/
def EPIPE : Nat := 32
/-- Invalid system call number (`include/uapi/asm-generic/errno.h`). -/
def ENOSYS : Nat := 38
/-- Operation not permitted (`include/uapi/asm-generic/errno-base.h`). -/
def EPERM : Nat := 1
/-- Out of memory (`include/uapi/asm-generic/errno-base.h`). -/
def ENOMEM : Nat := 12
/-- Permission denied (`include/uapi/asm-generic/errno-base.h`). -/
def EACCES : Nat := 13
/-- Device or resource busy (`include/uapi/asm-generic/errno-base.h`). -/
def EBUSY : Nat := 16
/-- File exists (`include/uapi/asm-generic/errno-base.h`). -/
def EEXIST : Nat := 17
/-- Invalid argument (`include/uapi/asm-generic/errno-base.h`). -/
def EINVAL : Nat := 22
/-- No such process (`include/uapi/asm-generic/errno-base.h`). -/
def ESRCH : Nat := 3
/-- File name too long (`include/uapi/asm-generic/errno.h`). -/
def ENAMETOOLONG : Nat := 36
/-- File too large (`include/uapi/asm-generic/errno-base.h`). -/
def EFBIG : Nat := 27
/-- Try again (`include/uapi/asm-generic/errno-base.h`). -/
def EAGAIN : Nat := 11
/-- No such device (`include/uapi/asm-generic/errno-base.h`). -/
def ENODEV : Nat := 19
/-- Text file busy (`include/uapi/asm-generic/errno-base.h`). -/
def ETXTBSY : Nat := 26
/-- Value too large for defined data type (`include/uapi/asm-generic/errno.h`). -/
def EOVERFLOW : Nat := 75
/-- Operation not supported (`include/uapi/asm-generic/errno.h`). -/
def EOPNOTSUPP : Nat := 95

/-- `s` with `rax` set to `v`. -/
def State.setRax (s : State) (v : BitVec 64) : State :=
  s.modCpu fun c => { c with gpr := c.gpr.set 0 v }

/-- The system call argument registers `rdi rsi rdx r10 r8 r9` (psABI A.2.1; the kernel's
`pt_regs` order in `arch/x86/entry/syscall_64.c`). -/
def syscallArgs (s : State) : List (BitVec 64) :=
  [s.cpu.gpr.rdi, s.cpu.gpr.rsi, s.cpu.gpr.rdx, s.cpu.gpr.r10, s.cpu.gpr.r8, s.cpu.gpr.r9]

/-- Finish a system call: result `ret` in `rax`, and its event. -/
def sysReturn (s : State) (ret : BitVec 64) (fromProc toProc : List Byte) : StepResult :=
  .running (s.setRax ret) (some ⟨s.cpu.gpr.rax, syscallArgs s, ret, fromProc, toProc⟩)

/-- A 32-bit argument (`int`, `unsigned int`): the low half of the register. -/
def arg32 (v : BitVec 64) : Nat := v.toNat % 2 ^ 32

/-- A signed 32-bit argument (`int`, `pid_t`). -/
def argInt (v : BitVec 64) : Int := (v.setWidth 32).toInt

/-- The number of bytes from `a` on, among `n`, that the kernel can write with user access rights
(`kernelWrite`'s check) before the first it cannot. -/
def writableLead (feat : Features) (s : State) (a : Addr) (n : Nat) : Nat :=
  ((List.range n).takeWhile fun i =>
    (a.add i).canonical feat.la57 && (s.proc.mm.mem.check feat s.cpu.pkru .write (a.add i)).isNone).length

/-- The number of bytes from `a` on, among `n`, that the kernel can read with user access rights
(`kernelRead`'s check) before the first it cannot. -/
def readableLead (feat : Features) (s : State) (a : Addr) (n : Nat) : Nat :=
  (firstRejected (fun i =>
    (a.add i).canonical feat.la57 && (s.proc.mm.mem.check feat s.cpu.pkru .read (a.add i)).isNone) 0 n).getD n

/-- `copy_to_user(a, bs)` (`arch/x86/include/asm/uaccess.h`, `copy_user_64.S`): the bytes `bs` go to
the process's memory at `a`, and the result says how many and whether all. A range that fails
`access_ok` gets none. The copy grows a stack where it must (`growFor`). When a byte in it cannot be
written, the copy stops at the fault having written a first part of `bs`, at most the bytes before the
first unwritable one; how many is not specified (the copy moves several bytes at a time), so it is a
choice (`Request.pick`). -/
def copyOut (prof : Profile) (s : State) (a : Addr) (bs : List Byte) : Req (State × Nat × Bool) :=
  if !accessOk prof.feat a bs.length then Pure.pure (s, 0, false) else do
  let s ← growFor prof s .write a bs.length
  match kernelWrite prof.feat s a bs with
  | some s' => Pure.pure (s', bs.length, true)
  | none => do
    let k ← Req.request (.pick (writableLead prof.feat s a bs.length))
    Pure.pure (s.withMem (writeBytes s.proc.mm.mem a (bs.take k.val)), k.val, false)

/-- `put_user(v, a)` of the bytes `bs` of a value of at most 8 bytes (`arch/x86/lib/putuser.S`): one
store, which writes all of them or none, so the result says whether it wrote them. A range that fails
`access_ok` gets none. The store grows a stack where it must (`growFor`). -/
def putUser (prof : Profile) (s : State) (a : Addr) (bs : List Byte) : Req (State × Bool) :=
  if !accessOk prof.feat a bs.length then Pure.pure (s, false) else do
  let s ← growFor prof s .write a bs.length
  match kernelWrite prof.feat s a bs with
  | some s' => Pure.pure (s', true)
  | none => Pure.pure (s, false)

/-- `copy_from_user` of `n` bytes at `a` (`get_user`, and `copy_from_user` whose caller fails on a
short copy): a range that fails `accessOk` gives none; otherwise the read grows a stack where it must
(`growFor`) and gives the bytes, or none if one cannot be read. With the state after the growths.
On x86-64 the kernel does not call `access_ok` here: it masks the pointer (`_inline_copy_from_user`,
`mask_user_address`; `get_user`'s `check_range`, `arch/x86/lib/getuser.S`), so that one above
`USER_PTR_MAX` becomes `USER_PTR_MAX`, the start of the unmapped page past user space, where the read
faults at once, and a range that crosses `USER_PTR_MAX` faults there. For at most a page, which every
caller reads, that is `accessOk`'s answer: such a range starts on the last page of user space, with no
mapping above it to grow, and its caller fails on the short copy. -/
def copyIn (prof : Profile) (s : State) (a : Addr) (n : Nat) : Req (State × Option (List Byte)) :=
  if !accessOk prof.feat a n then Pure.pure (s, none) else do
  let s ← growFor prof s .read a n
  Pure.pure (s, kernelRead prof.feat s a n)

/-- The largest value of the `fs.nr_open` setting (`fs/file.c` `sysctl_nr_open_max`: `INT_MAX`
rounded down to a multiple of `BITS_PER_LONG`, 64): no descriptor table grows to this many entries
(`expand_files`), so every descriptor is below it. -/
def nrOpenMax : Nat := 2147483584

/-- `PATH_MAX` (`include/uapi/linux/limits.h`): the size of a path name with its NUL. -/
def pathMax : Nat := 4096

/-- Where the path name at `a` ends, within `PATH_MAX` bytes: the offset of the first byte that is a
NUL, cannot be read by the kernel, or lies at or above `TASK_SIZE_MAX`, with `true` if that byte is
readable (then a NUL) and `false` otherwise; `none` if no such byte lies within `PATH_MAX`. -/
def pathEnd (feat : Features) (s : State) (a : Addr) : Option (Nat × Bool) :=
  let ok (i : Nat) : Bool := decide (a.toNat + i < userPtrMax feat) && (kernelRead feat s (a.add i) 1).isSome
  ((List.range pathMax).find? fun i => !ok i || s.proc.mm.mem.readByte (a.add i) == 0).map fun i => (i, ok i)

/-- A path name read from the process's memory at `a` (`getname_flags`, `strncpy_from_user`):
the bytes up to the first NUL, which must come within `PATH_MAX` bytes (else `ENAMETOOLONG`); a
byte up to it that the kernel cannot read, or that lies at or above `TASK_SIZE_MAX`, gives
`EFAULT`. An empty name is returned as such (the caller decides). With the state after the stack
growths of the reads (`growFor`): the kernel reads the name in order, so a byte on a page where it
grows a stack is a 0 of the grown page and ends the name. It reads a word of 8 bytes at a time
(`do_strncpy_from_user`; x86-64 has efficient unaligned access, so the words count from `a`), and so
also touches the bytes after the NUL up to the end of its word, which may grow a stack too. -/
def userPath (prof : Profile) (s : State) (a : Addr) : Req (State × Except Nat (List Byte)) :=
  match pathEnd prof.feat s a with
  | none => Pure.pure (s, .error ENAMETOOLONG)
  | some (i, _) => do
    let s ← growFor prof s .read a (i + 1)
    match pathEnd prof.feat s a with
    | some (j, true) => do
      let s ← growFor prof s .read (a.add (j + 1)) (8 * (j / 8 + 1) - (j + 1))
      Pure.pure (s, .ok (readBytes s.proc.mm.mem a j))
    | _ => Pure.pure (s, .error EFAULT)

end ZellicX86
