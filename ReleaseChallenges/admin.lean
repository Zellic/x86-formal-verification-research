import Glibc243UbuntuClients.Admin.Statement
-- The challenge: the theorem as this repository states it, without its proof (`sorry`). Lean warns that it
-- uses `sorry`: that is expected. `lake comparator` holds the proof export to exactly this statement and
-- refuses a proof that uses `sorry` (`checks/admin/verify-source.sh`, the README's "How to check").
theorem Clients.Admin.holds_proof : Clients.Admin.holds := by sorry
