import ZellicX86.Spec.Linux.Syscall.Common
/-!
# Linux system calls: clocks and the CPU

`clock_gettime`, `gettimeofday`, `time` and `getcpu`, whose work the vDSO's functions also do and on
which they fall back (`Spec/Vdso.lean`). What a clock reads is a request (`Request.clock`), and so are the time
zone and the CPU the thread runs on: the model has no time and no scheduler.

Sources: Linux v6.18 `kernel/time/posix-timers.c` (`clock_gettime`, `clockid_to_kclock`,
`posix_clocks`), `kernel/time/alarmtimer.c`, `kernel/time/time.c` (`gettimeofday`, `time`,
`put_timespec64`), `kernel/sys.c` (`getcpu`), `include/uapi/linux/time.h`.
-/
namespace ZellicX86

/-- The bytes of `struct __kernel_timespec` (`include/uapi/linux/time_types.h`): `tv_sec` and
`tv_nsec`, 8 bytes each. -/
def Timespec.bytes (t : Timespec) : List Byte :=
  toBytesLE t.sec 8 ++ toBytesLE (BitVec.ofNat 64 t.nsec.val) 8

/-- `clock_gettime(which_clock, tp)` (`kernel/time/posix-timers.c`); `which_clock` is a
`clockid_t`, a 32-bit `int`. The clocks of `posix_clocks`: `CLOCK_REALTIME` (0), `CLOCK_MONOTONIC`
(1), the process's and the thread's CPU time (2, 3), `CLOCK_MONOTONIC_RAW` (4), the coarse wall and
monotonic clocks (5, 6), `CLOCK_BOOTTIME` (7) and `CLOCK_TAI` (11) read the clock (`Request.clock`);
the alarm clocks (8, 9) read it on a machine with a real-time clock with alarms and fail with `EINVAL`
otherwise (`Request.rtcAlarm`). The time goes to `tp` (`put_timespec64`, `copy_to_user` of 16 bytes:
`EFAULT`, with a part written). Every other id is `EINVAL`, except negative ones (CPU-time clocks of
other processes and threads, and clocks of devices, by descriptor) and those of the auxiliary clocks
(16–23, with `CONFIG_POSIX_AUX_CLOCKS`), which are not modelled. -/
def sysClockGettime (prof : Profile) (s : State) : Req StepResult := do
  let id := argInt s.cpu.gpr.rdi
  let tp := s.cpu.gpr.rsi
  let fail (e : Nat) : Req StepResult := Pure.pure (sysReturn s (errRet e) [] [])
  let read (id : Nat) : Req StepResult := do
    let t ← Req.request (.clock id)
    let (s', _, all) ← copyOut prof s tp t.bytes
    Pure.pure (sysReturn s' (if all then 0 else errRet EFAULT) [] (if all then t.bytes else []))
  if id < 0 then
    Pure.pure (.stopped (.notModelled (.feature "clock_gettime of another task's CPU-time clock or a device's")))
  else
  let id := id.toNat
  if [0, 1, 2, 3, 4, 5, 6, 7, 11].contains id then read id
  else if id = 8 ∨ id = 9 then do
    let rtc : Bool ← Req.request .rtcAlarm
    if rtc then read id else fail EINVAL
  else if 16 ≤ id ∧ id < 24 then
    Pure.pure (.stopped (.notModelled (.feature "clock_gettime of an auxiliary clock")))
  else fail EINVAL

/-- `gettimeofday(tv, tz)` (`kernel/time/time.c`): unless `tv` is 0, the wall clock's seconds and
microseconds go to it, 8 bytes each, by one `put_user` each (`EFAULT` when one fails, after the
seconds if the microseconds' fails); then, unless `tz` is 0, the kernel's time zone, 8 bytes
(`copy_to_user`: `EFAULT`, with a part written). -/
def sysGettimeofday (prof : Profile) (s : State) : Req StepResult := do
  let tv := s.cpu.gpr.rdi
  let tz := s.cpu.gpr.rsi
  let fault (s' : State) : Req StepResult := Pure.pure (sysReturn s' (errRet EFAULT) [] [])
  let (s, out) ← if tv = 0 then Pure.pure (s, some []) else do
    let t ← Req.request (.clock 0)
    let sec := toBytesLE t.sec 8
    let usec := toBytesLE (BitVec.ofNat 64 (t.nsec.val / 1000)) 8
    let (s, ok) ← putUser prof s tv sec
    if !ok then Pure.pure (s, none) else do
    let (s, ok) ← putUser prof s (tv.add 8) usec
    Pure.pure (s, if ok then some (sec ++ usec) else none)
  match out with
  | none => fault s
  | some bs =>
    if tz = 0 then Pure.pure (sysReturn s 0 [] bs) else do
    let z ← Req.request .timezone
    let (s, _, all) ← copyOut prof s tz (toBytesLE z 8)
    if all then Pure.pure (sysReturn s 0 [] (bs ++ toBytesLE z 8)) else fault s

/-- `time(tloc)` (`kernel/time/time.c`): the wall clock's seconds (`ktime_get_real_seconds`), stored
at `tloc` unless it is 0 (`put_user`, 8 bytes: `EFAULT`), and returned. -/
def sysTime (prof : Profile) (s : State) : Req StepResult := do
  let tloc := s.cpu.gpr.rdi
  let t ← Req.request (.clock 0)
  if tloc = 0 then Pure.pure (sysReturn s t.sec [] []) else do
  let (s, ok) ← putUser prof s tloc (toBytesLE t.sec 8)
  if ok then Pure.pure (sysReturn s t.sec [] (toBytesLE t.sec 8))
  else Pure.pure (sysReturn s (errRet EFAULT) [] [])

/-- `getcpu(cpu, node, cache)` (`kernel/sys.c`): the CPU the thread runs on and its node
(`Request.cpuNode`: one of the machine's CPUs), each a 32-bit `unsigned`, stored at `cpu` and at `node` unless 0 (`put_user`;
both are tried, and `EFAULT` if either failed). `cache` is unused. -/
def sysGetcpu (prof : Profile) (s : State) : Req StepResult := do
  let pc := s.cpu.gpr.rdi
  let pn := s.cpu.gpr.rsi
  let ⟨(cpu, node), _⟩ ← Req.request (.cpuNode prof.cpus)
  let (s, ok₁) ← if pc = 0 then Pure.pure (s, true) else putUser prof s pc (toBytesLE cpu 4)
  let (s, ok₂) ← if pn = 0 then Pure.pure (s, true) else putUser prof s pn (toBytesLE node 4)
  if ok₁ ∧ ok₂ then Pure.pure (sysReturn s 0 []
    ((if pc = 0 then [] else toBytesLE cpu 4) ++ (if pn = 0 then [] else toBytesLE node 4)))
  else Pure.pure (sysReturn s (errRet EFAULT) [] [])

end ZellicX86
