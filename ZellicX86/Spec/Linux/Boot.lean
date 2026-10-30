import ZellicX86.Spec.Word
/-!
# Linux: the booted kernel's settings

Settings of the running kernel that the model of Linux reads and that no process can change: fixed
when the kernel was built (its configuration) or booted (its command line), the same for every process
and every step of a run. They are part of the machine a run executes on (`Profile.linux`), beside the
processor's description, and theorems quantify over them as over the rest of the profile.

Settings that a process or an administrator can change while a run goes on (`sysctl`s such as
`vm.mmap_min_addr`, the `init_pkru` file in debugfs) are not here: the model leaves them to the
environment, as requests, and `execve` takes the values it reads of them as its own input
(`KernelConfig`).

Sources: Linux v6.18 `mm/mmap.c`, `arch/x86/kernel/cpu/bus_lock.c`, `arch/x86/entry/vsyscall/vsyscall_64.c`,
`arch/x86/Kconfig`, `arch/x86/kernel/signal.c`, `arch/x86/kernel/fpu/xstate.h`,
`arch/x86/entry/vdso/vma.c`, `lib/vdso/datastore.c`.
-/
namespace ZellicX86

/-- What a locked access across a 64-byte cache line (a split lock) does in user mode, as the
`split_lock_detect=` option and the processor's detection give it (`arch/x86/kernel/cpu/bus_lock.c`). -/
inductive SplitLock
  /-- The access is atomic, as any locked access (SDM Vol. 3A, 11.1.2 "Bus Locking"): with
  `split_lock_detect=off`, with `warn` (the default where the processor detects split locks) or
  `ratelimit:N`, where the kernel lets the instruction run again after its `#AC` or `#DB`
  (`handle_user_split_lock`, `handle_bus_lock`), and on a processor without detection
  (`X86_FEATURE_SPLIT_LOCK_DETECT`, `X86_FEATURE_BUS_LOCK_DETECT`). Under a hypervisor the kernel does not
  enable split-lock detection (`split_lock_setup`), but KVM passes bus-lock detection through to its guests
  (`arch/x86/kvm/cpuid.c`, `BUS_LOCK_DETECT`), so a guest booted with `split_lock_detect=fatal` may be `trap`. -/
  | atomic
  /-- `split_lock_detect=fatal` on a processor that detects split locks (`X86_FEATURE_SPLIT_LOCK_DETECT`):
  `#AC` before the instruction runs, which ends in `SIGBUS` with `BUS_ADRALN` (`exc_alignment_check`). -/
  | fault
  /-- `split_lock_detect=fatal` on a processor that detects only bus locks
  (`X86_FEATURE_BUS_LOCK_DETECT`): the instruction runs, and a `#DB` trap after it sends `SIGBUS`
  (`handle_bus_lock`). Not modelled. -/
  | trap
  deriving DecidableEq, Repr

/-- How the kernel treats the legacy `vsyscall` page at `0xffffffffff600000` (`vsyscall=`,
`arch/x86/entry/vsyscall/vsyscall_64.c`; the default is `CONFIG_LEGACY_VSYSCALL_XONLY` or
`CONFIG_LEGACY_VSYSCALL_NONE`). The emulate mode maps a readable, non-executable page; in the
xonly and none modes no page-table entry gives user mode access to it (`map_vsyscall`). -/
inductive Vsyscall
  /-- `vsyscall=xonly`: an instruction fetched at the start of the page's entry points is emulated
  (`emulate_vsyscall`); every other access faults. The only entry points are offsets
  0, 0x400 and 0x800 (`addr_to_vsyscall_nr`). -/
  | xonly
  /-- `vsyscall=emulate`: the fixed page is readable, not writable or executable; valid
  entry-point fetches are emulated (`map_vsyscall`, `emulate_vsyscall`). -/
  | emulate
  /-- `vsyscall=none`: every access faults, fetches too. -/
  | none
  deriving DecidableEq, Repr

/-- The settings of the booted Linux kernel that the model reads. A field's default is that of a mainline
kernel built with its default configuration (`arch/x86/Kconfig`) and booted without options; for
`cpuidFault`, `splitLock` and `xsaves`, which also depend on the processor, the default is one common
choice, not a property of every machine. A default matters only where a statement uses it. -/
structure LinuxBoot where
  /-- `stack_guard_gap` in pages (`mm/mmap.c`): how far below a growing stack a mapping that does not
  grow down and allows some access must end (`growStack`). The boot option `stack_guard_gap=N` sets it
  to `N` pages (`cmdline_parse_stack_guard_gap`, as bytes `N << PAGE_SHIFT` in an `unsigned long`, so a
  multiple of the page size below `2 ^ 64`); without it, 256 pages. -/
  stackGuardGap : Nat := 256
  /-- The kernel's boot CPU has `X86_FEATURE_CPUID_FAULT`, permitting a thread to disable
  `CPUID` with `arch_prctl(ARCH_SET_CPUID)` (`arch/x86/kernel/process.c`,
  `set_cpuid_mode`). This is the kernel's capability, including feature overrides, rather than
  a raw `CPUID` bit; without it the call returns `ENODEV`. -/
  cpuidFault : Bool := false
  /-- What a split lock does (`SplitLock`). -/
  splitLock : SplitLock := .atomic
  /-- How the `vsyscall` page is treated (`Vsyscall`). -/
  vsyscall : Vsyscall := .xonly
  /-- The kernel checks an alternate signal stack's size strictly (`CONFIG_STRICT_SIGALTSTACK_SIZE`, or
  `strict_sas_size=1`; `arch/x86/kernel/signal.c` `sigaltstack_size_valid`): `sigaltstack` refuses a stack
  too small for a signal frame (`setAltStack`). -/
  strictSasSize : Bool := false
  /-- The kernel is built with 32-bit emulation (`CONFIG_IA32_EMULATION`): its largest signal frame has
  room for a 32-bit process's x87 state (`fpu__get_fpstate_size`), which the strict size check
  subtracts (`sigaltstack_size_valid`), and which the size it reports counts (`AT_MINSIGSTKSZ`,
  `Profile.sigframeMax`). -/
  ia32Emulation : Bool := true
  /-- The kernel keeps the extended state with `XSAVES` and `XRSTORS` (`X86_FEATURE_XSAVES`: the
  processor has them, `CPUID.(EAX=0DH,ECX=1):EAX[3]`, and the command line has no `noxsaves`;
  `arch/x86/kernel/fpu/xstate.h` `os_xrstor`), so the compacted form, rather than `XRSTOR`'s standard one,
  restores its initial state (`fpuRestore`). -/
  xsaves : Bool := true
  /-- The vDSO is mapped (`vdso64_enabled`; `vdso=0` on the command line turns it off). It is six
  data pages (`[vvar]`, 4 pages, and `[vvar_vclock]`, 2 pages) and then its image (`[vdso]`), readable
  and executable (`arch/x86/entry/vdso/vma.c` `map_vdso`): the image's code runs as any code of the
  process. -/
  vdso : Bool := true
  /-- Which of the vDSO's six data pages have a source (`lib/vdso/datastore.c` `vvar_fault`,
  `vvar_vclock_fault`): the time data; the time-namespace page, only in a time namespace; the
  random-number data; the architecture's data, if the kernel has any; the paravirtual and the
  Hyper-V clock pages, only with that clock in use. A read of a page without one raises
  `SIGBUS`. -/
  vdsoData : Fin 6 → Bool
  /-- The pages of the vDSO's image, an ELF shared object linked at address 0 (`vdso64.so`), which depend
  on how the kernel was built: each page's 4096 bytes (a `Frame`, `Spec/Memory.lean`). Its dynamic symbol
  table names the entry points of its functions (`LinuxBoot.vdsoEntry`, `Spec/Vdso.lean`). -/
  vdsoText : List (BitVec 12 → Byte)
  /-- The kernel is built with `CONFIG_COMPAT_BRK` ("Disable heap randomization"; `mm/Kconfig`):
  without randomization, `brk` then accepts breaks down to the end of the data segment
  (`mm/mmap.c` `brk`, `min_brk`). -/
  compatBrk : Bool

end ZellicX86
