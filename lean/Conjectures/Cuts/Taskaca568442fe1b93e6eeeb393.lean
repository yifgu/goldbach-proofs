import Mathlib

/-! # PREPUB twin-primes: `L-twin-primes-cut-aca568442fe1b93e6eeeb393`

Premise 2/2 of a cut of `L-twin-primes-cut-2b5a8c39956bd7392fecdf97`.
-/

theorem Conjectures.Cuts.Taskaca568442fe1b93e6eeeb393 : ∀ (x1 : ℕ), (-1 : ℤ) < (x1 : ℤ) := by
  intro x1
  have h : (0 : ℤ) ≤ (x1 : ℤ) := Int.natCast_nonneg x1
  linarith
