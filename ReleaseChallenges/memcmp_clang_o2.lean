import Examples.Memcmp.Statement
-- The challenge: the theorem as this repository states it, without its proof (`sorry`). Lean warns that it
-- uses `sorry`: that is expected. `lake comparator` holds the proof export to exactly this statement and
-- refuses a proof that uses `sorry` (`checks/memcmp-clang-o2/verify-source.sh`, the README's "How to check").
theorem Memcmp.clangO2_holds : Memcmp.holds Memcmp.clangO2 := by sorry
