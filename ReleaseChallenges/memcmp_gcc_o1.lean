import Examples.Memcmp.Statement
-- The challenge: the theorem as this repository states it, without its proof (`sorry`). Lean warns that it
-- uses `sorry`: that is expected. `lake comparator` holds the proof export to exactly this statement and
-- refuses a proof that uses `sorry` (`checks/memcmp-gcc-o1/verify-source.sh`, the README's "How to check").
theorem Memcmp.gccO1_holds : Memcmp.holds Memcmp.gccO1 := by sorry
