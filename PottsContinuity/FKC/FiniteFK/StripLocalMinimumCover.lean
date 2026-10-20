-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/StripLocalMinimumCover.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.StripLocalMinimum
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- Horizontal indices in the zero-tilt strip window supplied by the local-minimum bound. -/
def stripHeightWindow (n m : ℕ) : Finset ℤ :=
  Finset.Icc (-(↑(n * m) : ℤ)) (↑(n * m))

/-- Candidate lattice sites in the inclusive lower half of the zero-tilt strip window. -/
def stripHeightCandidates (n m : ℕ) : Finset (ℤ × ℕ) :=
  stripHeightWindow n m ×ˢ Finset.Icc 0 n

theorem stripHeightWindow_card (n m : ℕ) :
    (stripHeightWindow n m).card = 2 * (n * m) + 1 := by
  change (Finset.Icc (-(↑(n * m) : ℤ)) (↑(n * m))).card = _
  rw [Int.card_Icc]
  have hcast : (↑(n * m) : ℤ) + 1 - (-(↑(n * m) : ℤ)) =
      ↑(2 * (n * m) + 1) := by push_cast; omega
  rw [hcast, Int.toNat_natCast]

theorem stripHeightCandidates_card (n m : ℕ) :
    (stripHeightCandidates n m).card = (2 * (n * m) + 1) * (n + 1) := by
  rw [stripHeightCandidates, Finset.card_product, stripHeightWindow_card, Nat.card_Icc]
  simp

/-- The finite set of sites contains the graph point `(k, f k)` whenever `k` lies
in the local-minimum window and its height is in the inclusive range `0,…,n`. -/
theorem stripHeightGraphPoint_mem_candidates {n m : ℕ} {f : ℤ → ℕ} {k : ℤ}
    (hk : k.natAbs ≤ n * m) (hfk : f k ≤ n) :
    (k, f k) ∈ stripHeightCandidates n m := by
  rw [stripHeightCandidates, Finset.mem_product]
  constructor
  · have hkabs : |k| ≤ (↑(n * m) : ℤ) := by
      calc
        |k| = (k.natAbs : ℤ) := (Int.natCast_natAbs k).symm
        _ ≤ (↑(n * m) : ℤ) := by exact_mod_cast hk
    exact Finset.mem_Icc.mpr (abs_le.mp hkabs)
  · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hfk⟩

end PottsContinuity.FKC.FiniteFK
