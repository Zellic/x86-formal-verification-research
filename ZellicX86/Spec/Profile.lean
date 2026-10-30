import ZellicX86.Spec.Linux.Boot
/-!
# The CPU profile

Everything about the processor that is fixed for a run but differs between conforming
machines: vendor, supported features, what `CPUID` reports on each CPU, `XCR0`, and behaviour
the manuals leave to the implementation; and, beside it, the booted kernel's own settings
(`LinuxBoot`, `Spec/Linux/Boot.lean`). Theorems quantify over profiles; a target's needs appear
as hypotheses ("the CPU has BMI1"). Values that may differ from one event to the next (undefined flags,
the time-stamp counter, which CPU an instruction executes on) are not here but requests
(`Spec/Request.lean`).
-/
namespace ZellicX86

/-- Processor vendor. Where Intel's and AMD's manuals differ, the model branches on this. -/
inductive Vendor
  | intel
  | amd
  deriving DecidableEq, Repr

/-- CPU features that change what an instruction does or whether it decodes: each field says that
the processor executes the forms of the feature, with the state the kernel enabled for it (`XCR0`,
`CR4`). Each names the `CPUID` flag that reports the feature (SDM Vol. 2, "CPUID", Table 3-8 and
following; APM Vol. 3, Appendix E), but a field is not that flag: a set flag means the processor
has the feature (`Profile.Consistent`), while a clear one leaves it open, since a hypervisor may clear
the flag of a feature the processor still executes. `nx` and `la57` are the kernel's choices; `Consistent` does not
tie them to a `CPUID` flag. -/
structure Features where
  /-- `CPUID.01H:ECX.SSSE3[bit 9]`. -/
  ssse3 : Bool
  /-- `CPUID.01H:ECX.SSE4_1[bit 19]`. -/
  sse41 : Bool
  /-- `CPUID.(EAX=07H,ECX=0):EBX.SHA[bit 29]`. -/
  sha : Bool
  /-- `CPUID.(EAX=07H,ECX=0):EBX.BMI1[bit 3]`. Without it `F3 0F BC` executes as `BSF`. -/
  bmi1 : Bool
  /-- `CPUID.80000001H:ECX.LZCNT[bit 5]` (AMD: ABM). Without it `F3 0F BD` executes as `BSR`. -/
  lzcnt : Bool
  /-- AVX usable: `CPUID.01H:ECX.AVX[bit 28]` and the OS enabled YMM state in `XCR0`. -/
  avx : Bool
  /-- AVX-512 usable: `CPUID.(EAX=07H,ECX=0):EBX.AVX512F[bit 16]` and the OS enabled the
  opmask and ZMM state in `XCR0`. -/
  avx512f : Bool
  /-- APX usable (the `REX2` prefix `D5`): `CPUID.(EAX=07H,ECX=1):EDX.APX_F[bit 21]` and
  enabled in `XCR0`. -/
  apx : Bool
  /-- Protection keys for user pages usable (`CPUID.(EAX=07H,ECX=0):ECX.OSPKE[bit 4]`). -/
  pku : Bool
  /-- The execute-disable bit is in use (`CPUID.80000001H:EDX.NX[bit 20]`; Linux enables it
  whenever the CPU has it). Without it, every readable page is executable. -/
  nx : Bool
  /-- 5-level paging is enabled (`CR4.LA57`): linear addresses are 57 bits wide. Linux enables it at
  boot on CPUs with LA57 (`CPUID.(EAX=07H,ECX=0):ECX[bit 16]`) unless the command line has `no5lvl`
  (`arch/x86/boot/compressed/pgtable_64.c` `configure_5level_paging`, `arch/x86/boot/startup/map_kernel.c`
  `check_la57_support`). -/
  la57 : Bool
  /-- `CPUID.01H:ECX.SSE4_2[bit 20]`. -/
  sse42 : Bool
  /-- `CPUID.(EAX=07H,ECX=0):EBX.BMI2[bit 8]`. -/
  bmi2 : Bool
  /-- AVX2 usable: `CPUID.(EAX=07H,ECX=0):EBX.AVX2[bit 5]` and `avx`. -/
  avx2 : Bool
  /-- AVX-512 byte and word instructions usable: `CPUID.(EAX=07H,ECX=0):EBX.AVX512BW[bit 30]`
  and `avx512f`. -/
  avx512bw : Bool
  /-- AVX-512 doubleword and quadword instructions usable:
  `CPUID.(EAX=07H,ECX=0):EBX.AVX512DQ[bit 17]` and `avx512f`. -/
  avx512dq : Bool
  /-- AVX-512 at vector lengths 128 and 256 usable: `CPUID.(EAX=07H,ECX=0):EBX.AVX512VL[bit 31]`
  and `avx512f`. -/
  avx512vl : Bool
  /-- `CPUID.01H:ECX.MOVBE[bit 22]`. -/
  movbe : Bool
  /-- `CPUID.80000001H:EDX.RDTSCP[bit 27]`. -/
  rdtscp : Bool
  /-- `CPUID.01H:ECX.SSE3[bit 0]` (`FISTTP`, SSE3 arithmetic and duplication moves). -/
  sse3 : Bool
  /-- `CPUID.01H:ECX.FMA[bit 12]`; usable with AVX enabled (SDM Vol. 1, 14.5.3; APM Vol. 3, CPUID). -/
  fma : Bool
  /-- `CPUID.(EAX=07H,ECX=0):ECX.CET_SS[bit 7]`: the processor implements CET shadow stacks, whose
  instructions (`INCSSP`, `RDSSP`, …) it then executes (SDM Vol. 1, ch. 18; Vol. 2, "INCSSPD/INCSSPQ").
  Linux enables a shadow stack per thread (`ThreadK.shstk`). -/
  cetSs : Bool
  /-- `CPUID.(EAX=07H,ECX=0):EBX.RTM[bit 11]`: the processor implements Restricted Transactional Memory
  (`XBEGIN`, `XEND`, `XABORT`, `XTEST`; SDM Vol. 1, 17.3.1.2). A processor whose RTM Linux or its
  firmware disabled may report the flag clear (`IA32_TSX_CTRL.TSX_CPUID_CLEAR`, SDM Vol. 4, Table 2-2;
  `arch/x86/kernel/cpu/tsx.c`) and still execute the instructions. AMD processors have no RTM. -/
  rtm : Bool
  /-- `CPUID.(EAX=07H,ECX=0):EBX.HLE[bit 4]`: the processor implements Hardware Lock Elision, the prefix
  hints `XACQUIRE` (`F2`) and `XRELEASE` (`F3`) on the instructions SDM Vol. 2, "XACQUIRE/XRELEASE"
  lists, which may then run a critical section as a transaction, and `XTEST` (SDM Vol. 1, 17.3.1.1,
  17.3.1.3). Without HLE those prefixes are ignored. Clear flags leave it open as for `rtm`. -/
  hle : Bool
  deriving Repr, Inhabited

/-- What Linux tells a new process about the processor in its auxiliary vector
(`fs/binfmt_elf.c` `create_elf_tables`, `arch/x86/include/asm/elf.h`). These are values the
kernel computed at boot, from `cpuid` and the features it enabled. -/
structure AuxCpu where
  /-- `AT_HWCAP`: the boot CPU's `CPUID.01H:EDX` as the kernel left it (`ELF_HWCAP`,
  `boot_cpu_data.x86_capability[CPUID_1_EDX]`). Not tied to `Profile.cpuid`: the kernel clears and
  sets bits of this word at boot, for errata (`PSE`, `PAT`, `MCE` and others in
  `arch/x86/kernel/cpu/`), for the local APIC it enabled or disabled (`arch/x86/kernel/apic/apic.c`)
  and by the command line (`clearcpuid=`, `setcpuid=`, `arch/x86/kernel/cpu/common.c`). -/
  hwcap : BitVec 32
  /-- `AT_HWCAP2` (`elf_hwcap2`): bit 0 `ring3mwait` enabled (`arch/x86/kernel/cpu/intel.c`), bit 1
  `FSGSBASE` enabled (`arch/x86/kernel/cpu/common.c` `identify_cpu`; the boot option `nofsgsbase` clears
  the feature first). Not tied to `Profile.cpuid`: choices of the kernel, which the model reads nowhere
  else. -/
  hwcap2 : BitVec 32
  /-- `AT_MINSIGSTKSZ`: the largest signal frame the kernel may build (`get_sigframe_size`), which
  depends on the size of the `XSAVE` state the kernel enabled (`Profile.sigframeMax`, `Consistent`). -/
  minSigStkSz : Nat
  deriving Repr

/-- What `CPUID` writes to `EAX`, `EBX`, `ECX`, `EDX` (SDM Vol. 2, "CPUID"; APM Vol. 3, "CPUID"). -/
structure CpuidResult where
  eax : BitVec 32
  ebx : BitVec 32
  ecx : BitVec 32
  edx : BitVec 32

/-- The processor a run executes on, with the settings of the kernel booted on it (`linux`). -/
structure Profile where
  vendor : Vendor
  feat : Features
  aux : AuxCpu
  /-- The number of the machine's logical CPUs as the kernel numbers them (`nr_cpu_ids`; one if 0): every
  CPU the process runs on during the run, whatever its affinity, is one of `0` to `cpus - 1`. -/
  cpus : Nat
  /-- What `CPUID` returns on logical CPU `cpu` (0 to `cpus - 1`) for leaf `EAX = leaf` and
  subleaf `ECX = subleaf`; a leaf that ignores `ECX` gives the same for every subleaf. Per CPU:
  APIC ids differ between CPUs, and on hybrid parts the core type and the cache leaves differ
  between core types. What the flags settle about `feat`, `xcr0` and `aux` is `Consistent`. -/
  cpuid : (cpu : Nat) → (leaf subleaf : BitVec 32) → CpuidResult
  /-- `XCR0`, the state components the kernel enabled for `XSAVE` at boot
  (`fpu__init_cpu_xstate`, `arch/x86/kernel/fpu/xstate.c`); `none` if it did not enable `XSAVE`
  (`CR4.OSXSAVE = 0`, as on a CPU without it). -/
  xcr0 : Option (BitVec 64)
  /-- The `MXCSR` bits the processor supports (`MXCSR_MASK`, which `FXSAVE` and `XSAVE` store; SDM
  Vol. 1, 11.6.6): loading a value with another bit set raises `#GP`. Bit 17 set means AMD's
  misaligned SSE mode exists (`MXCSR.MM`, `Profile.misalignSse`; APM Vol. 1, 4.2.2). -/
  mxcsrMask : BitVec 32
  /-- What `RDTSCP` reads as `TSC_AUX` on logical CPU `cpu` (0 to `cpus - 1`, as for `cpuid`): the
  value Linux writes into `MSR_TSC_AUX` at boot on a CPU with `RDTSCP` or `RDPID`, the kernel's CPU
  number in bits 11–0 and its NUMA node above them (`arch/x86/kernel/cpu/common.c` `setup_getcpu`,
  `vdso_encode_cpunode` in `arch/x86/include/asm/segment.h`). A theorem that relies on the encoding
  assumes it. -/
  tscAux : (cpu : Nat) → BitVec 32
  /-- On an Intel processor: `FDP` changes only at an x87 instruction that incurs an unmasked exception
  ("FDP_EXCPTN_ONLY", SDM Vol. 1, 8.1.8), which `CPUID.(EAX=07H,ECX=0):EBX[6]` reports (`Consistent`).
  Not read on an AMD processor, for which the bit is reserved (APM Vol. 3, `CPUID Fn0000_0007_EBX_x0`). -/
  fdpExcptnOnly : Bool
  /-- On an Intel processor: the x87 selectors `FCS` and `FDS` are deprecated, stored as 0000H (SDM
  Vol. 1, 8.1.8: "the processor deprecates FCS and FDS; it saves each as 0000H"; Vol. 2, "FXSAVE",
  Tables 3-48 and 3-49), which `CPUID.(EAX=07H,ECX=0):EBX[13]` reports (`Consistent`). Not read on an AMD
  processor, for which the bit is reserved. -/
  fcsDeprecated : Bool
  /-- On an AMD processor: `XRSTOR` and `FXRSTOR` always restore the x87 error pointers from the save
  area, and `XSAVE` and `FXSAVE` store them, or 0 when no `#MF` is pending (APM Vol. 2, 11.5.10: "the
  error pointer fields in the save area are zeroed if there is no pending #MF"); without the feature,
  they are neither saved nor restored unless a `#MF` is pending. `CPUID Fn8000_0008_EBX[2]`
  ("RstrFpErrPtrs") reports it (`Consistent`). Not read on an Intel processor, whose save and restore
  always keep them. -/
  amdErrPtrs : Bool
  /-- The booted Linux kernel's settings that the model reads (`LinuxBoot`), Linux's part of the
  machine: what the processor's instructions read is in the fields above, as the kernel configured
  it. -/
  linux : LinuxBoot

/-- Bit `i` of the register `r` (`CpuidResult.eax`, …) of `CPUID` leaf `leaf`, subleaf `sub` is set on
some CPU of `prof`. -/
def Profile.reports (prof : Profile) (leaf sub : BitVec 32) (r : CpuidResult → BitVec 32) (i : Nat) :
    Prop :=
  ∃ cpu, cpu < max prof.cpus 1 ∧ (r (prof.cpuid cpu leaf sub)).getLsbD i = true

/-- Every bit set in `w` some CPU of `prof` reports in register `r` of `CPUID` leaf `leaf`, subleaf `sub` (`reports`),
not necessarily the same CPU for every bit: `w` is that register as one of the CPUs answered, a word with fewer bits
set (0, say), or the union of several CPUs' answers. What a statement says of a `CPUID` word a program stored and
reads back later. -/
def Profile.Reported (prof : Profile) (leaf sub : BitVec 32) (r : CpuidResult → BitVec 32) (w : BitVec 32) : Prop :=
  ∀ i, w.getLsbD i = true → prof.reports leaf sub r i

/-- The kernel enabled the state components `m` in `XCR0` (`xcr0`; none without `XSAVE`). -/
def Profile.enabled (prof : Profile) (m : BitVec 64) : Prop :=
  prof.xcr0.getD 0 &&& m = m

/-- The size the kernel gives the largest signal frame (`AT_MINSIGSTKSZ`), as it computes it at boot
(`arch/x86/kernel/signal.c` `init_sigframe_size`; `arch/x86/kernel/fpu/signal.c`
`fpu__get_fpstate_size`): the largest frame structure (`struct sigframe_ia32`, 736 bytes, with
`CONFIG_IA32_EMULATION`; else `struct rt_sigframe`, 440 bytes), 15 bytes of alignment, the user
`XSAVE` area (`fpu_user_cfg.max_size`: `CPUID.(EAX=0DH,ECX=0):EBX` for what `XCR0` enabled, read on
the boot processor, here CPU 0, `get_xsave_size_user`; 512 bytes of `FXSAVE` without `XSAVE`) with
the 4 bytes of `FP_XSTATE_MAGIC2` after an `XSAVE` area, the 112-byte `fregs_state` with
`CONFIG_IA32_EMULATION`, and 63 bytes of alignment, rounded up to a multiple of 16. -/
def Profile.sigframeMax (prof : Profile) : Nat :=
  let ia32 := prof.linux.ia32Emulation
  let fp := match prof.xcr0 with
    | some _ => (prof.cpuid 0 0xD 0).ebx.toNat + 4
    | none => 512
  let n := (if ia32 then 736 else 440) + 15 + fp + (if ia32 then 112 else 0) + 63
  (n + 15) / 16 * 16

/-- The state components AVX needs enabled in `XCR0`: SSE (1) and AVX (2) (SDM Vol. 1, 14.3). -/
def xcr0Avx : BitVec 64 := 0x6

/-- The state components AVX-512 needs enabled in `XCR0`: SSE, AVX, opmask (5), `ZMM_Hi256` (6) and
`Hi16_ZMM` (7) (SDM Vol. 1, 15.2). -/
def xcr0Avx512 : BitVec 64 := 0xE6

/-- The state component APX needs enabled in `XCR0`: the extended general registers (19) (SDM Vol. 1,
3.1.1.1 and 13.1). -/
def xcr0Apx : BitVec 64 := 0x80000

/-- What a processor's `CPUID` bits settle about the rest of its profile, one way (SDM Vol. 2, "CPUID";
APM Vol. 3, "CPUID" and Appendix E): a bit set on any of its CPUs (`reports`), with the state the kernel
enabled in `XCR0` for the feature where it needs one (`enabled`), means the processor has the feature
or behaviour the bit reports, while a clear bit leaves it open, since a hypervisor may clear bits of
what the processor still does. An inconsistent profile describes no real machine. One `feat` for all
CPUs: a machine whose CPUs differ in what they execute is not described by a `Profile`, and a bit set on
one of its CPUs makes the field hold for all.

Not tied here: `nx` and `la57` (the kernel's choices, which no flag reports), `aux.hwcap` and
`aux.hwcap2` (see `AuxCpu`), `mxcsrMask` and `tscAux`. `XCR0` is tied to the flag `OSXSAVE`, which reports
that the kernel enabled `XSAVE` (`CR4.OSXSAVE`); `AT_MINSIGSTKSZ` is what the kernel computes from
`CPUID` leaf `0DH` (`sigframeMax`). And leaf 1, which has no subleaves, answers the same for every `ECX`
(`noSubleaf`). -/
structure Profile.Consistent (prof : Profile) : Prop where
  /-- `CPUID.01H:ECX.SSE3[0]`. -/
  sse3 : prof.reports 1 0 (·.ecx) 0 → prof.feat.sse3 = true
  /-- `CPUID.01H:ECX.SSSE3[9]`. -/
  ssse3 : prof.reports 1 0 (·.ecx) 9 → prof.feat.ssse3 = true
  /-- `CPUID.01H:ECX.FMA[12]`, with AVX's state enabled. -/
  fma : prof.reports 1 0 (·.ecx) 12 → prof.enabled xcr0Avx → prof.feat.fma = true
  /-- `CPUID.01H:ECX.SSE4_1[19]`. -/
  sse41 : prof.reports 1 0 (·.ecx) 19 → prof.feat.sse41 = true
  /-- `CPUID.01H:ECX.SSE4_2[20]`. -/
  sse42 : prof.reports 1 0 (·.ecx) 20 → prof.feat.sse42 = true
  /-- `CPUID.01H:ECX.MOVBE[22]`. -/
  movbe : prof.reports 1 0 (·.ecx) 22 → prof.feat.movbe = true
  /-- `CPUID.01H:ECX.OSXSAVE[27]`: the kernel enabled `XSAVE`, so `XGETBV` reads `XCR0`. -/
  osxsave : prof.reports 1 0 (·.ecx) 27 → prof.xcr0.isSome = true
  /-- `CPUID.01H:ECX.AVX[28]`, with AVX's state enabled. -/
  avx : prof.reports 1 0 (·.ecx) 28 → prof.enabled xcr0Avx → prof.feat.avx = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.BMI1[3]`. -/
  bmi1 : prof.reports 7 0 (·.ebx) 3 → prof.feat.bmi1 = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.AVX2[5]`, with AVX's state enabled. -/
  avx2 : prof.reports 7 0 (·.ebx) 5 → prof.enabled xcr0Avx → prof.feat.avx2 = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.BMI2[8]`. -/
  bmi2 : prof.reports 7 0 (·.ebx) 8 → prof.feat.bmi2 = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.AVX512F[16]`, with AVX-512's state enabled. -/
  avx512f : prof.reports 7 0 (·.ebx) 16 → prof.enabled xcr0Avx512 → prof.feat.avx512f = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.AVX512DQ[17]`, with AVX-512's state enabled. -/
  avx512dq : prof.reports 7 0 (·.ebx) 17 → prof.enabled xcr0Avx512 → prof.feat.avx512dq = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.SHA[29]`. -/
  sha : prof.reports 7 0 (·.ebx) 29 → prof.feat.sha = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.AVX512BW[30]`, with AVX-512's state enabled. -/
  avx512bw : prof.reports 7 0 (·.ebx) 30 → prof.enabled xcr0Avx512 → prof.feat.avx512bw = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.AVX512VL[31]`, with AVX-512's state enabled. -/
  avx512vl : prof.reports 7 0 (·.ebx) 31 → prof.enabled xcr0Avx512 → prof.feat.avx512vl = true
  /-- `CPUID.(EAX=07H,ECX=0):ECX.OSPKE[4]`: the kernel enabled protection keys (`CR4.PKE`). -/
  pku : prof.reports 7 0 (·.ecx) 4 → prof.feat.pku = true
  /-- `CPUID.(EAX=07H,ECX=0):ECX.CET_SS[7]`. -/
  cetSs : prof.reports 7 0 (·.ecx) 7 → prof.feat.cetSs = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.RTM[11]`. -/
  rtm : prof.reports 7 0 (·.ebx) 11 → prof.feat.rtm = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX.HLE[4]`. -/
  hle : prof.reports 7 0 (·.ebx) 4 → prof.feat.hle = true
  /-- `CPUID.(EAX=07H,ECX=1):EDX.APX_F[21]`, with APX's state enabled. -/
  apx : prof.reports 7 1 (·.edx) 21 → prof.enabled xcr0Apx → prof.feat.apx = true
  /-- `CPUID.80000001H:ECX.LZCNT[5]` (AMD: ABM). -/
  lzcnt : prof.reports 0x80000001 0 (·.ecx) 5 → prof.feat.lzcnt = true
  /-- `CPUID.80000001H:EDX.RDTSCP[27]`. -/
  rdtscp : prof.reports 0x80000001 0 (·.edx) 27 → prof.feat.rdtscp = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX[6]` on an Intel processor: `FDP` changes only at unmasked
  exceptions. -/
  fdpExcptnOnly : prof.vendor = .intel → prof.reports 7 0 (·.ebx) 6 → prof.fdpExcptnOnly = true
  /-- `CPUID.(EAX=07H,ECX=0):EBX[13]` on an Intel processor: `FCS` and `FDS` are deprecated. -/
  fcsDeprecated : prof.vendor = .intel → prof.reports 7 0 (·.ebx) 13 → prof.fcsDeprecated = true
  /-- `CPUID Fn8000_0008_EBX[2]` on an AMD processor: the error pointers are always saved and
  restored. -/
  amdErrPtrs : prof.vendor = .amd → prof.reports 0x80000008 0 (·.ebx) 2 → prof.amdErrPtrs = true
  /-- `AT_MINSIGSTKSZ` is what the kernel computes (`sigframeMax`). -/
  minSigStkSz : prof.aux.minSigStkSz = prof.sigframeMax
  /-- Leaf `01H`, whose flags the fields above read at subleaf 0, ignores `ECX` (SDM Vol. 2, "CPUID", Table 3-8 and APM
  Vol. 3, Appendix E: it has no subleaves): code that executes `CPUID` for it without setting `ECX` (glibc's
  `get_common_indices`) gets the subleaf-0 answer. Not claimed of the extended leaves `8000_0001H` and `8000_0008H`:
  above the maximum extended leaf an Intel processor answers with the highest basic leaf's data (SDM Vol. 2, "CPUID",
  the note on invalid input values), which may depend on `ECX` (`0DH`, `1FH`). -/
  noSubleaf : ∀ cpu, cpu < max prof.cpus 1 → ∀ sub, prof.cpuid cpu 1 sub = prof.cpuid cpu 1 0

end ZellicX86
