import Glibc243Ubuntu.MemrchrStatement
-- The challenge: the theorem as this repository states it, without its proof (`sorry`). Lean warns that it
-- uses `sorry`: that is expected. `lake comparator` holds the proof export to exactly this statement and
-- refuses a proof that uses `sorry` (`checks/memrchr-avx2/verify-source.sh`, the README's "How to check").
theorem Glibc243Ubuntu.Memrchr.avx2_holds : Glibc243Ubuntu.Memrchr.avx2Holds := by sorry
