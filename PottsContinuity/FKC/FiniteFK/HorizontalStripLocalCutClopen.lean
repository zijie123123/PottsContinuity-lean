-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalCutClopen.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightLocalization
public import PottsContinuity.FKC.FiniteFK.FreePlaneFinitePatternEnergy
public import Mathlib.Topology.Clopen
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

noncomputable section

open Set PottsContinuity.FKC.FiniteFK

def horizontalStripClosedCutPairEvent (n : ℕ) (l r : ℤ) :
    Set LatticeConfiguration :=
  {ω | ∀ e ∈ horizontalStripCutEdges n l ∪ horizontalStripCutEdges n r,
    ω e = false}

private theorem horizontalStripClosedCutPairEvent_isClopen
    (n : ℕ) (l r : ℤ) :
    IsClopen (horizontalStripClosedCutPairEvent n l r) := by
  simpa [horizontalStripClosedCutPairEvent, finiteOriginalEdgePatternEvent,
    Finset.mem_union] using
      (finiteOriginalEdgePatternEvent_isClopen
        (horizontalStripCutEdges n l ∪ horizontalStripCutEdges n r)
        (fun _ => false))

def horizontalStripLocalCutPairIndex (M : ℕ) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ Set.Icc (-(M : ℤ)) (-1) ∧ p.2 ∈ Set.Icc 0 ((M : ℤ) - 1)}

private theorem horizontalStripLocalCutPairIndex_finite (M : ℕ) :
    (horizontalStripLocalCutPairIndex M).Finite := by
  have hprod :
      (Set.Icc (-(M : ℤ)) (-1) ×ˢ Set.Icc 0 ((M : ℤ) - 1)).Finite := by
    classical
    exact Set.toFinite _
  exact hprod.subset fun p hp => hp

private theorem horizontalStripLocalClosedCutSuccess_eq_biUnion
    (M n : ℕ) :
    horizontalStripLocalClosedCutSuccess M n =
      ⋃ p ∈ horizontalStripLocalCutPairIndex M,
        horizontalStripClosedCutPairEvent n p.1 p.2 := by
  ext ω
  constructor
  · rintro ⟨l, hMl, hl0, r, hr0, hrM, hcl, hcr⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(l, r), Set.mem_iUnion.mpr ?_⟩
    have hidx : (l, r) ∈ horizontalStripLocalCutPairIndex M := by
      simp [horizontalStripLocalCutPairIndex, Set.mem_Icc]
      constructor <;> omega
    refine ⟨hidx, ?_⟩
    change ∀ e ∈ horizontalStripCutEdges n l ∪ horizontalStripCutEdges n r,
      ω e = false
    intro e he
    simp only [Finset.mem_union] at he
    rcases he with he | he
    · exact hcl e he
    · exact hcr e he
  · intro hω
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hω
    obtain ⟨hidx, hpair⟩ := Set.mem_iUnion.mp hp
    rcases p with ⟨l, r⟩
    have hidx0 : (-(M : ℤ) ≤ l ∧ l ≤ -1) ∧ 0 ≤ r ∧ r < (M : ℤ) := by
      simpa [horizontalStripLocalCutPairIndex, Set.mem_Icc] using hidx
    have hidx' : -(M : ℤ) ≤ l ∧ l ≤ -1 ∧ 0 ≤ r ∧ r ≤ (M : ℤ) - 1 := by
      rcases hidx0 with ⟨⟨hl, hl1⟩, hr0, hrM⟩
      exact ⟨hl, hl1, hr0, by omega⟩
    change ∀ e ∈ horizontalStripCutEdges n l ∪ horizontalStripCutEdges n r,
      ω e = false at hpair
    refine ⟨l, hidx'.1, by omega, r, hidx'.2.2.1, by omega, ?_, ?_⟩
    · intro e he
      exact hpair e (Finset.mem_union.mpr (Or.inl he))
    · intro e he
      exact hpair e (Finset.mem_union.mpr (Or.inr he))

theorem isClopen_horizontalStripLocalClosedCutSuccess
    (M n : ℕ) : IsClopen (horizontalStripLocalClosedCutSuccess M n) := by
  rw [horizontalStripLocalClosedCutSuccess_eq_biUnion]
  exact (horizontalStripLocalCutPairIndex_finite M).isClopen_biUnion fun p hp =>
    horizontalStripClosedCutPairEvent_isClopen n p.1 p.2

theorem isClopen_horizontalStripLocalClosedCutFailure
    (M n : ℕ) : IsClopen ((horizontalStripLocalClosedCutSuccess M n)ᶜ) :=
  (isClopen_horizontalStripLocalClosedCutSuccess M n).compl

end
end PottsContinuity.FKC.Medial
