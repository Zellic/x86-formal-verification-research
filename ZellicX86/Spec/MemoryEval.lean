import ZellicX86.Spec.Memory
/-!
# Evaluating memory searches

Nothing here changes what the model means: the theorem `Memory.nextMapped_eq_nextMappedFast` makes
compiled code (`#eval`, `#guard`) compute `Memory.nextMapped` by
`Memory.nextMappedFast`, which skips the pages outside the memory's cover (`Memory.cover`) instead of
looking at each. Proofs never evaluate the search, and an auditor needs only the theorem's statement:
the two are equal. It sits in `Spec` because the compiler applies such a (`@[csimp]`) theorem only to code
compiled after it, and the model's own searches (`stackAbove`, `Spec/Linux/Stack.lean`) must be compiled
after it.

`firstRejected` finds the first index of a range at which a test fails, looking no further. The model's
stack growth (`Spec/Linux/Stack.lean`) and the system calls' check of how much of a buffer the kernel can
read (`Spec/Linux/Syscall/Common.lean`) use it, so that evaluation stops at the first inaccessible byte.
`firstRejected_eq_find` and `firstRejected_getD` state what it computes.
-/
namespace ZellicX86

/-- The first page number from `q` on that lies in a run of `rs`, with the end of that run: pages from
`q` up to before it lie in no run (`firstCovered_spec`). Empty runs are skipped. -/
def firstCovered : List (Nat × Nat) → Nat → Option (Nat × Nat)
  | [], _ => none
  | (f, n) :: rs, q =>
    if 0 < n ∧ q < f + n then
      let c := max f q
      match firstCovered rs q with
      | some (c', s') => if c' < c then some (c', s') else some (c, f + n)
      | none => some (c, f + n)
    else firstCovered rs q

/-- The first mapped page among those from `q` up to before `e`: pages before `stop` one by one, then from
the next page in the cover on (`firstCovered`), one by one to the end of its run. -/
def Memory.nextMappedFrom (mem : Memory) (q e stop : Nat) : Option (Nat × Mapping) :=
  if q < e then
    if q < stop then
      match mem.mapAt q with
      | some m => some (q, m)
      | none => mem.nextMappedFrom (q + 1) e stop
    else
      match firstCovered mem.cover q with
      | none => none
      | some (c, s) =>
        if c < e then
          match mem.mapAt c with
          | some m => some (c, m)
          | none => mem.nextMappedFrom (max (c + 1) (q + 1)) e s
        else none
  else none
termination_by e - q

/-- `Memory.nextMapped` over the cover. -/
def Memory.nextMappedFast (mem : Memory) (p n : Nat) : Option (Nat × Mapping) :=
  mem.nextMappedFrom (p + 1) (p + 1 + n) (p + 1)

theorem firstCovered_spec : ∀ (rs : List (Nat × Nat)) (q : Nat),
    match firstCovered rs q with
    | none => ∀ x, q ≤ x → inRuns rs x = false
    | some (c, _) => q ≤ c ∧ ∀ x, q ≤ x → x < c → inRuns rs x = false
  | [], q => by simp [firstCovered, inRuns]
  | (f, n) :: rs, q => by
    have ih := firstCovered_spec rs q
    unfold firstCovered
    by_cases hq : 0 < n ∧ q < f + n
    · simp only [hq, and_self, ↓reduceIte]
      cases hr : firstCovered rs q with
      | none =>
        rw [hr] at ih
        refine ⟨Nat.le_max_right _ _, fun x h₁ h₂ => ?_⟩
        simp only [inRuns, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
        exact ⟨by simp; omega, ih x h₁⟩
      | some cs =>
        obtain ⟨c', s'⟩ := cs
        rw [hr] at ih
        simp only
        by_cases hc : c' < max f q
        · simp only [hc, ↓reduceIte]
          refine ⟨ih.1, fun x h₁ h₂ => ?_⟩
          simp only [inRuns, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
          exact ⟨by simp; omega, ih.2 x h₁ h₂⟩
        · simp only [hc, ↓reduceIte]
          refine ⟨Nat.le_max_right _ _, fun x h₁ h₂ => ?_⟩
          simp only [inRuns, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
          exact ⟨by simp; omega, ih.2 x h₁ (by omega)⟩
    · simp only [hq, ↓reduceIte]
      cases hr : firstCovered rs q with
      | none =>
        rw [hr] at ih
        intro x h₁
        simp only [inRuns, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
        exact ⟨by simp; omega, ih x h₁⟩
      | some cs =>
        obtain ⟨c', s'⟩ := cs
        rw [hr] at ih
        refine ⟨ih.1, fun x h₁ h₂ => ?_⟩
        simp only [inRuns, List.any_cons, Bool.or_eq_false_iff] at ih ⊢
        exact ⟨by simp; omega, ih.2 x h₁ h₂⟩

/-- A page outside the cover is unmapped. -/
theorem Memory.mapAt_of_not_inRuns (mem : Memory) {x : Nat} (h : inRuns mem.cover x = false) :
    mem.mapAt x = none := by
  unfold Memory.mapAt
  split
  · next hx =>
    cases hm : mem.map (BitVec.ofNat 52 x) with
    | none => rfl
    | some m =>
      have := mem.covers (BitVec.ofNat 52 x) (by rw [hm]; rfl)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, h] at this
      cases this
  · rfl

/-- Unmapped pages after `p` are skipped. -/
theorem Memory.nextMapped_skip (mem : Memory) :
    ∀ (j p k : Nat), (∀ i, i < j → mem.mapAt (p + 1 + i) = none) →
      mem.nextMapped p (j + k) = mem.nextMapped (p + j) k
  | 0, p, k, _ => by simp
  | j + 1, p, k, h => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    conv => lhs; unfold Memory.nextMapped
    rw [show mem.mapAt (p + 1) = none by simpa using h 0 (by omega)]
    simp only
    rw [mem.nextMapped_skip j (p + 1) k fun i hi => by rw [show p + 1 + 1 + i = p + 1 + (i + 1) by omega]; exact h (i + 1) (by omega)]
    rw [show p + 1 + j = p + (j + 1) by omega]

/-- Unmapped pages only: none. -/
theorem Memory.nextMapped_none (mem : Memory) :
    ∀ (k p : Nat), (∀ i, i < k → mem.mapAt (p + 1 + i) = none) → mem.nextMapped p k = none
  | 0, _, _ => rfl
  | k + 1, p, h => by
    unfold Memory.nextMapped
    rw [show mem.mapAt (p + 1) = none by simpa using h 0 (by omega)]
    exact mem.nextMapped_none k (p + 1) fun i hi => by
      rw [show p + 1 + 1 + i = p + 1 + (i + 1) by omega]; exact h (i + 1) (by omega)

theorem Memory.nextMappedFrom_eq (mem : Memory) :
    ∀ (n p stop : Nat), mem.nextMappedFrom (p + 1) (p + 1 + n) stop = mem.nextMapped p n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro p stop
  rw [Memory.nextMappedFrom]
  by_cases hn : p + 1 < p + 1 + n
  · simp only [hn, ↓reduceIte]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    by_cases hst : p + 1 < stop
    · simp only [hst, ↓reduceIte]
      conv => rhs; unfold Memory.nextMapped
      cases hm : mem.mapAt (p + 1) with
      | some m => rfl
      | none =>
        simp only
        have := ih n' (by omega) (p + 1) stop
        rw [show p + 1 + (n' + 1) = p + 1 + 1 + n' by omega, this]
    · simp only [hst, ↓reduceIte]
      have hs := firstCovered_spec mem.cover (p + 1)
      cases hc : firstCovered mem.cover (p + 1) with
      | none =>
        rw [hc] at hs
        exact (mem.nextMapped_none _ p fun i _ => mem.mapAt_of_not_inRuns (hs _ (by omega))).symm
      | some cs =>
        obtain ⟨c, s⟩ := cs
        rw [hc] at hs
        obtain ⟨hqc, hgap⟩ := hs
        simp only
        by_cases hce : c < p + 1 + (n' + 1)
        · simp only [hce, ↓reduceIte]
          have hskip := mem.nextMapped_skip (c - (p + 1)) p (n' + 1 - (c - (p + 1)))
            fun i hi => mem.mapAt_of_not_inRuns (hgap _ (by omega) (by omega))
          rw [show c - (p + 1) + (n' + 1 - (c - (p + 1))) = n' + 1 by omega] at hskip
          rw [hskip, show n' + 1 - (c - (p + 1)) = (n' + 1 - (c - (p + 1)) - 1) + 1 by omega]
          conv => rhs; unfold Memory.nextMapped
          rw [show p + (c - (p + 1)) + 1 = c by omega]
          cases hm : mem.mapAt c with
          | some m => rfl
          | none =>
            simp only
            rw [show max (c + 1) (p + 1 + 1) = c + 1 by omega]
            have := ih (n' + 1 - (c - (p + 1)) - 1) (by omega) c s
            rw [show p + 1 + (n' + 1) = c + 1 + (n' + 1 - (c - (p + 1)) - 1) by omega, this]
        · simp only [hce, ↓reduceIte]
          exact (mem.nextMapped_none _ p fun i hi => mem.mapAt_of_not_inRuns (hgap _ (by omega) (by omega))).symm
  · simp only [hn, ↓reduceIte]
    rw [show n = 0 by omega]; rfl

theorem Memory.nextMappedFast_eq (mem : Memory) (n p : Nat) : mem.nextMappedFast p n = mem.nextMapped p n :=
  mem.nextMappedFrom_eq n p (p + 1)

/-- The page map `f` on the pages of the runs `rs` and nothing elsewhere: a page map whose cover is `rs`
(`mapOn_covers`), for building memories to evaluate. -/
def mapOn (rs : List (Nat × Nat)) (f : PageNum → Option Mapping) (p : PageNum) : Option Mapping :=
  if inRuns rs p.toNat then f p else none

theorem mapOn_covers {rs : List (Nat × Nat)} {f : PageNum → Option Mapping} :
    ∀ p, (mapOn rs f p).isSome = true → inRuns rs p.toNat = true := by
  intro p h
  unfold mapOn at h
  split at h
  · assumption
  · cases h

/-- Evaluation computes `Memory.nextMapped` over the cover. -/
@[csimp] theorem Memory.nextMapped_eq_nextMappedFast :
    @Memory.nextMapped = @Memory.nextMappedFast := by
  funext mem p n
  exact (mem.nextMappedFast_eq n p).symm

/-- First rejected index in `[start, start + n)`, stopping as soon as `ok` is false.
This scans the kernel's byte-access range without allocating a list for bytes after a fault.
`firstRejected_eq_find` identifies it with the increasing finite-list search. -/
def firstRejected (ok : Nat → Bool) (start : Nat) : Nat → Option Nat
  | 0 => none
  | n + 1 => if ok start then firstRejected ok (start + 1) n else some start

/-- The short-circuit scan has exactly the finite-list search's result. -/
theorem firstRejected_eq_find (ok : Nat → Bool) (start n : Nat) :
    firstRejected ok start n = (List.range' start n).find? (fun i => !ok i) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    cases h : ok start <;> simp [firstRejected, List.range'_succ, h, ih]

/-- The rejected index, or the range's end if none, is the end of its allowed prefix. -/
theorem firstRejected_getD (ok : Nat → Bool) (start n : Nat) :
    (firstRejected ok start n).getD (start + n) = start + ((List.range' start n).takeWhile ok).length := by
  induction n generalizing start with
  | zero => simp [firstRejected]
  | succ n ih =>
    cases h : ok start
    · simp [firstRejected, List.range'_succ, h]
    · have he : start + (n + 1) = (start + 1) + n := by omega
      simp only [firstRejected, h, ↓reduceIte, List.range'_succ, List.takeWhile_cons,
        List.length_cons]
      rw [he, ih]
      omega

end ZellicX86
