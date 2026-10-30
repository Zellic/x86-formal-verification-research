import ZellicX86.Spec.Statement
import ZellicX86.Spec.Vdso
import ZellicX86.Spec.Lib.C.Start
import ZellicX86.Spec.VdsoImages
import Glibc243Ubuntu.TunablesEnv
import Glibc243Ubuntu.Heap.MemGranted
/-!
# Statement: the demonstrations' carve-outs, for any program

A demonstration theorem (admin's and admin2's `holds`, `Admin/Statement.lean`, `Admin2/Statement.lean`) states what a
program does for a restricted class of launches, processors and kernels, each restriction a named hypothesis, a
*carve-out*. Those that do not depend on the program are here, so
that every program's demonstration names the same ones: the processor (`ThisProcessor`: the development VM's virtual
CPU as far as glibc's startup asks), the launches (`DemoArgs`: not secure, no tunables, no `LD_LIBRARY_PATH`), the
kernel's vDSO (`ThisVdso`) and the runs (`DemoRuns`). A program's demonstration names them (admin's `Statement.lean` exports
them into its namespace); what depends on the program (its allocator's link values, the exit's handlers' registry, its
memory limits) stays in its own statement.
-/
namespace Glibc243Ubuntu.Program.Demo
open ZellicX86 Glibc243Ubuntu

/-! ## The processor -/

/-- The development VM's virtual CPU's answers to the `CPUID` queries glibc 2.43's static startup can make
(`init_cpu_features`, `update_active`, `dl_init_cacheinfo` with `handle_amd`, `handle_intel`, `handle_zhaoxin`:
`sysdeps/x86/cpu-features.c`, `sysdeps/x86/dl-cacheinfo.h`), each a leaf, a subleaf and the four registers: leaves 0, 1,
2, 4 (subleaves 0–7), 7 (0, 1), 0xB (0–3), 0xD (0–31), 0x14, 0x19, 0x24, 0x80000000, 0x80000001, 0x80000005–0x80000008,
0x8000001D (0–7). Recorded on all 25 logical CPUs of the development VM (a KVM guest on an AMD Ryzen 9 7950X3D, Zen 4;
kernel 6.18): the virtual CPU's answers, with the hypervisor bit (leaf 1 `ECX` bit 31) and the VM's topology (leaves
0xB, 0x80000008), which a bare-metal part does not give. They answer alike but for the APIC ids (leaf 1 `EBX` bits
24–31, leaf 0xB `EDX`), recorded as 0 here. Leaves above the highest basic one (0x10) answer 0. -/
def cpuidRecord : List (BitVec 32 × BitVec 32 × CpuidResult) :=
  [(0x0, 0x0, ⟨0x10, 0x68747541, 0x444d4163, 0x69746e65⟩),
   (0x1, 0x0, ⟨0xa60f12, 0x200800, 0xfff83203, 0x178bfbff⟩),
   (0x2, 0x0, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x0, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x1, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x2, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x3, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x4, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x5, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x6, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x4, 0x7, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x7, 0x0, ⟨0x1, 0xf1bf07ab, 0x405f5e, 0xbc000010⟩),
   (0x7, 0x1, ⟨0x20, 0x0, 0x0, 0x0⟩),
   (0xb, 0x0, ⟨0x0, 0x1, 0x100, 0x0⟩),
   (0xb, 0x1, ⟨0x5, 0x20, 0x200, 0x0⟩),
   (0xb, 0x2, ⟨0x0, 0x0, 0x2, 0x0⟩),
   (0xb, 0x3, ⟨0x0, 0x0, 0x3, 0x0⟩),
   (0xd, 0x0, ⟨0x2e7, 0x988, 0x988, 0x0⟩),
   (0xd, 0x1, ⟨0xf, 0x988, 0x0, 0x0⟩),
   (0xd, 0x2, ⟨0x100, 0x240, 0x0, 0x0⟩),
   (0xd, 0x3, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x4, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x5, ⟨0x40, 0x340, 0x0, 0x0⟩),
   (0xd, 0x6, ⟨0x200, 0x380, 0x0, 0x0⟩),
   (0xd, 0x7, ⟨0x400, 0x580, 0x0, 0x0⟩),
   (0xd, 0x8, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x9, ⟨0x8, 0x980, 0x0, 0x0⟩),
   (0xd, 0xa, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0xb, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0xc, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0xd, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0xe, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0xf, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x10, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x11, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x12, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x13, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x14, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x15, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x16, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x17, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x18, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x19, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x1a, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x1b, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x1c, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x1d, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x1e, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0xd, 0x1f, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x14, 0x0, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x19, 0x0, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x24, 0x0, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x80000000, 0x0, ⟨0x80000022, 0x68747541, 0x444d4163, 0x69746e65⟩),
   (0x80000001, 0x0, ⟨0xa60f12, 0x0, 0xc003f7, 0x2fd3fbff⟩),
   (0x80000005, 0x0, ⟨0xff48ff40, 0xff48ff40, 0x20080140, 0x20080140⟩),
   (0x80000006, 0x0, ⟨0x5c002200, 0x6c004200, 0x4006140, 0x2009140⟩),
   (0x80000007, 0x0, ⟨0x0, 0x0, 0x0, 0x100⟩),
   (0x80000008, 0x0, ⟨0x302e, 0x1302d205, 0xa01f, 0x0⟩),
   (0x8000001d, 0x0, ⟨0x4121, 0x1c0003f, 0x3f, 0x0⟩),
   (0x8000001d, 0x1, ⟨0x4122, 0x1c0003f, 0x3f, 0x0⟩),
   (0x8000001d, 0x2, ⟨0x4143, 0x1c0003f, 0x7ff, 0x2⟩),
   (0x8000001d, 0x3, ⟨0x3c163, 0x3c0003f, 0x7fff, 0x1⟩),
   (0x8000001d, 0x4, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x8000001d, 0x5, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x8000001d, 0x6, ⟨0x0, 0x0, 0x0, 0x0⟩),
   (0x8000001d, 0x7, ⟨0x0, 0x0, 0x0, 0x0⟩)]

/-- A processor's answer `r` to leaf `leaf`, subleaf `sub`, agrees with the recorded `e`, except:
- APIC ids: leaf 1's `EBX[31:24]` and leaf 0xB's `EDX` (SDM Vol. 2A, CPUID; APM Vol. 3, `CPUID Fn0000_0001_EBX`,
  `Fn0000_000B_EDX`).
- L3 size: legacy leaf `0x80000006`'s `EDX[31:18]` (size in 512 KiB units) and modern leaf
  `0x8000001D`, subleaf 3's entire `ECX` (number of sets minus one). The legacy associativity, line size and reserved
  bits stay recorded (`0x3ffff` masks out only the size); modern geometry stays recorded in `EAX`/`EBX`/`EDX`.
  APM Vol. 3, Appendix E, `Fn8000_0006_EDX` and `Fn8000_001D`. -/
def SameAnswer (leaf sub : BitVec 32) (r e : CpuidResult) : Prop :=
  r.eax = e.eax ∧ (if leaf = 1 then r.ebx &&& 0xffffff = e.ebx &&& 0xffffff else r.ebx = e.ebx) ∧
    (if leaf = 0x8000001d ∧ sub = 3 then True else r.ecx = e.ecx) ∧
    (leaf = 0xb ∨ if leaf = 0x80000006 then r.edx &&& 0x3ffff = e.edx &&& 0x3ffff else r.edx = e.edx)

/-- The leaves of `cpuidRecord` that have no subleaves (SDM rev. 092 Vol. 1 Ch. 21, Tables 21-4, 21-5, 21-11; APM
Vol. 3, Appendix E): 0, 1, 2, `0x80000000`, `0x80000001`, `0x80000005` to `0x80000008`. A processor answers them the same
whatever `ECX` holds (leaf 2 is reserved on AMD, APM App. E.3.3: there this rests on the measurement below),
and glibc's startup reads them with `ECX` as the code before left it (`__cpuid`: `init_cpu_features`' first `CPUID`,
leaf 0, is reached with `ECX` as `__tunables_init` returned it); recorded at subleaf 0. Checked on the development VM:
the same answers for nine values of `ECX` on five of its CPUs. -/
def subleaflessLeaves : List (BitVec 32) :=
  [0x0, 0x1, 0x2, 0x80000000, 0x80000001, 0x80000005, 0x80000006, 0x80000007, 0x80000008]

/-- **Demonstration carve-out**: the processor is the development VM's virtual CPU (a KVM guest on an AMD Ryzen 9
7950X3D; a bare-metal 7950X3D does not meet it), as far as glibc's startup asks: an AMD
one, every logical CPU of which answers each query of `cpuidRecord` as recorded but for the APIC ids and L3 size
fields (`SameAnswer`), a query of a leaf without subleaves (`subleaflessLeaves`) whatever its subleaf, with the kernel having enabled the x87,
SSE, AVX, AVX-512 (opmask, `ZMM_Hi256`, `Hi16_ZMM`) and PKRU state components in `XCR0` (`0x2e7`, as `XGETBV` read it
there) and `FSGSBASE` for user mode in `AT_HWCAP2` (`0x2`, as the VM's auxiliary vector has it). It makes glibc's
feature-dependent startup choices fixed while allowing cache-size thresholds to vary. A theorem using this predicate
covers the processors it describes. -/
def ThisProcessor (prof : Profile) : Prop :=
  prof.vendor = .amd ∧ prof.xcr0 = some 0x2e7 ∧ prof.aux.hwcap2 = 2 ∧
    ∀ cpu, cpu < max prof.cpus 1 → ∀ q ∈ cpuidRecord, ∀ sub, (sub = q.2.1 ∨ q.1 ∈ subleaflessLeaves) →
      SameAnswer q.1 sub (prof.cpuid cpu q.1 sub) q.2.2

/-! ## The launch -/

/-- The environment variables through which glibc 2.43's `__tunables_init` sets tunables (`elf/dl-tunables.c`):
`GLIBC_TUNABLES` and the aliases of this build's tunables (`env_alias` in `dl-tunables.list`:
`Tunables.tunables`). -/
def tunableVars : List String :=
  ["GLIBC_TUNABLES", "LD_PREFER_MAP_32BIT_EXEC", "MALLOC_ARENA_MAX", "MALLOC_ARENA_TEST", "MALLOC_CHECK_",
    "MALLOC_MMAP_MAX_", "MALLOC_MMAP_THRESHOLD_", "MALLOC_PERTURB_", "MALLOC_TOP_PAD_", "MALLOC_TRIM_THRESHOLD_"]

/-- No string of the environment `envp` sets one of `tunableVars`: none begins with such a name followed by `=`
(`tunable_is_name`, the test `__tunables_init` makes). Every tunable then keeps its default. -/
def NoTunables (envp : List (List Byte)) : Prop :=
  ∀ s ∈ envp, ∀ v ∈ tunableVars, ¬ Tunables.bytesOf (v ++ "=") <+: s

/-- **Demonstration carve-out**: the launches of the demonstration, `a` the arguments, environment and credentials
`execve` started the process with: not secure (`AT_SECURE` 0: no set-user-ID or set-group-ID file, no file
capabilities), no tunables set (`NoTunables`), no `LD_LIBRARY_PATH`. With every tunable
at its default, the theorems need no hypothesis about the tunables' values. -/
def DemoArgs (a : ExecArgs) : Prop :=
  a.secure = false ∧ NoTunables a.envp ∧ a.envVals "LD_LIBRARY_PATH" = []

/-! ## The kernel's vDSO -/

/-- **Demonstration carve-out**: the booted kernel maps no vDSO, or the development machine's image (Linux
6.18.35's, `VdsoImages.dev6_18_35`: its ELF tables, two pages), whose tables glibc's startup reads
(`_dl_non_dynamic_init`'s `setup_vdso`), as the demonstration assumes the development machine's processor
(`ThisProcessor`). -/
def ThisVdso (lb : LinuxBoot) : Prop :=
  lb.vdso = false ∨ VdsoImage lb VdsoImages.dev6_18_35 VdsoImages.dev6_18_35Pages

/-! ## The runs -/

/-- **Demonstration carve-out**, the runs: undisturbed, `/proc/self/exe` procfs's link, and the kernel never refusing
memory for want of it (`Heap.MemGranted`; placement checks can still fail independently); admin's `DemoEnv`. -/
def DemoRuns (o : Oracle) : Prop := (Undisturbed o ∧ ProcSelfExe o) ∧ Heap.MemGranted o

end Glibc243Ubuntu.Program.Demo
