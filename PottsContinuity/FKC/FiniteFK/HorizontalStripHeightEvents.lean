-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightEvents.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripGoodEvent
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Clopen
public import PottsContinuity.FKC.FiniteFK.StripLocalMinimumCover
public import Mathlib.Tactic

@[expose] public section

open Set Topology
namespace PottsContinuity.FKC.Medial
noncomputable section

/-- The finite family of source-good-event indices allowed by the deterministic
height bound and by the finite candidate window. -/
abbrev horizontalStripGoodCandidate (n m : ℕ) :=
  {x : ℤ × ℕ // x ∈ PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m ∧ x.2 ≤ n}

/-- Every configuration whose origin-column least height is at most `n` lies
in one of the finitely many literal source good events indexed by the candidate
set from the deterministic strip local-minimum lemma. -/
theorem horizontalStripHeightLE_at_zero_subset_goodEvents
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    {ω | horizontalStripHeight n ω 0 ≤ n} ⊆
      ⋃ x : horizontalStripGoodCandidate n m,
        horizontalStripGoodEvent n m x.1.1 x.1.2 x.2.2 := by
  classical
  intro ω h0
  let f : ℤ → ℕ := fun l => horizontalStripHeight n ω l
  obtain ⟨k, hk, hfk0, hlocal⟩ :=
    PottsContinuity.FKC.FiniteFK.exists_local_minimum_on_integer_strip f n m (by simpa [f] using h0)
  have hfk : f k ≤ n := le_trans hfk0 (by simpa [f] using h0)
  have hcandidate : (k, f k) ∈ PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m :=
    PottsContinuity.FKC.FiniteFK.stripHeightGraphPoint_mem_candidates hk hfk
  let x : horizontalStripGoodCandidate n m := ⟨(k, f k), hcandidate, hfk⟩
  have hgood : ω ∈ horizontalStripGoodEvent n m x.1.1 x.1.2 x.2.2 := by
    have hlocal' : ∀ l : ℤ, (l - k).natAbs ≤ m →
        horizontalStripHeight n ω k ≤ horizontalStripHeight n ω l := by
      simpa [f] using hlocal
    have hmembership := horizontalStripLocalMinimum_mem_goodEvent
      n m ω k hn hm (by simpa [f] using hfk) hlocal'
    simpa [x, f] using hmembership
  exact Set.mem_iUnion.mpr ⟨x, hgood⟩

end
end PottsContinuity.FKC.Medial
