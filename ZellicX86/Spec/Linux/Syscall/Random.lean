import ZellicX86.Spec.Linux.Syscall.Common
/-!
# Linux system calls: `getrandom`

How many bytes the call returns, or its error, is one request (`Request.randomCount`), and the bytes
another (`Request.randomBytes`): a theorem that holds for every answer holds for every output of the
kernel's generator. A statement about a probabilistic or adversarial game can instead interpret the
requests (`Req.interp`) with the bytes drawn uniformly, whatever count is chosen; that interpretation
is then what the statement assumes of the generator.

Sources: Linux v6.18 `drivers/char/random.c` (`getrandom`, `get_random_bytes_user`),
`lib/iov_iter.c` (`import_ubuf`), `include/uapi/linux/random.h`, `getrandom(2)`.
-/
namespace ZellicX86

/-- `getrandom(buf, len, flags)` (`drivers/char/random.c`); `flags` is 32-bit. Flags beyond
`GRND_NONBLOCK` (1), `GRND_RANDOM` (2) and `GRND_INSECURE` (4), or `GRND_RANDOM` with
`GRND_INSECURE`, are `EINVAL`. The environment then answers how many bytes, at most `len` (at most
`MAX_RW_COUNT`), or an error (`Request.randomCount`): the kernel fails only before its generator is
ready (`EAGAIN` with `GRND_NONBLOCK`, or a signal while it waits), and returns fewer bytes only when
a signal is pending; the model allows either answer at any time. Then the bytes (`Request.randomBytes`).
The buffer must pass `access_ok` (`EFAULT`). The bytes are copied to `buf`; a copy that faults
returns the number of bytes copied, or `EFAULT` if none. -/
def sysGetrandom (prof : Profile) (s : State) : Req StepResult := do
  let buf := s.cpu.gpr.rdi
  let n := min s.cpu.gpr.rsi.toNat maxRwCount
  let flags := arg32 s.cpu.gpr.rdx
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  if flags ≥ 8 ∨ flags / 2 % 4 = 3 then fail EINVAL else
  match ← Req.request (.randomCount n) with
  | .error e => fail e.val
  | .ok k =>
    let ⟨bs, _⟩ ← Req.request (.randomBytes k.val)
    if !accessOk prof.feat buf n then fail EFAULT else
    let (s', c, _) ← copyOut prof s buf bs
    if c = 0 ∧ bs ≠ [] then Pure.pure (sysReturn s' (errRet EFAULT) [] [])
    else Pure.pure (sysReturn s' (BitVec.ofNat 64 c) [] (bs.take c))

end ZellicX86
