import Examples.Memcmp.Statement
-- The challenge: the theorem as this repository states it, without its proof (`sorry`). Lean warns that it
-- uses `sorry`: that is expected. `lake comparator` holds the proof export to exactly this statement and
-- refuses a proof that uses `sorry` (`checks/memcmp-gcc-os/verify-source.sh`, the README's "How to check").
theorem Memcmp.gccOs_holds : Memcmp.holds Memcmp.gccOs := by sorry
