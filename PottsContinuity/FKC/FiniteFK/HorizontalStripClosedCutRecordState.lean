-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutRecordState.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutExploration
public import PottsContinuity.FKC.FiniteFK.AdaptiveDomainMarkov

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripClosedCutRecordStateEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripClosedCutRecordStateEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

private theorem finset_inter_eq_of_subset_agree
    {E : Type*} [DecidableEq E] (A B R T : Finset E)
    (hT : T ⊆ R) (hAgree : B ∩ R = A ∩ R) : B ∩ T = A ∩ T := by
  ext e
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨heB, heT⟩
    have heR := hT heT
    have hiff := congrArg (fun S : Finset E => e ∈ S) hAgree
    have heA : e ∈ A := by
      have : e ∈ B ∩ R := Finset.mem_inter.mpr ⟨heB, heR⟩
      exact (Finset.mem_inter.mp (hiff.mp this)).1
    exact ⟨heA, heT⟩
  · rintro ⟨heA, heT⟩
    have heR := hT heT
    have hiff := congrArg (fun S : Finset E => e ∈ S) hAgree
    have heB : e ∈ B := by
      have : e ∈ A ∩ R := Finset.mem_inter.mpr ⟨heA, heR⟩
      exact (Finset.mem_inter.mp (hiff.mpr this)).1
    exact ⟨heB, heT⟩

/-- Agreement on the revealed edges fixes both the tested sets and first-hit
indices of the actual left and right cut scans. -/
theorem horizontalStripClosedCutScans_eq_of_agree
    (N n K : ℕ) (A B : Finset (horizontalStripCutRectangle N n).edgeSet)
    (hKN : K ≤ N)
    (hAgree : B ∩ horizontalStripClosedCutReveal N n K A =
      A ∩ horizontalStripClosedCutReveal N n K A) :
    horizontalStripLeftBlockScan N n K B = horizontalStripLeftBlockScan N n K A ∧
      horizontalStripRightBlockScan N n K B = horizontalStripRightBlockScan N n K A := by
  have hTest := horizontalStripClosedCutReveal_contains_tested N n K A hKN
  have hLeftSubset : (horizontalStripLeftBlockScan N n K A).1 ⊆
      horizontalStripClosedCutReveal N n K A := by
    intro e he
    exact hTest (Finset.mem_union.mpr (Or.inl he))
  have hRightSubset : (horizontalStripRightBlockScan N n K A).1 ⊆
      horizontalStripClosedCutReveal N n K A := by
    intro e he
    exact hTest (Finset.mem_union.mpr (Or.inr he))
  have hAgreeL := finset_inter_eq_of_subset_agree A B
    (horizontalStripClosedCutReveal N n K A)
    (horizontalStripLeftBlockScan N n K A).1 hLeftSubset hAgree
  have hAgreeR := finset_inter_eq_of_subset_agree A B
    (horizontalStripClosedCutReveal N n K A)
    (horizontalStripRightBlockScan N n K A).1 hRightSubset hAgree
  exact ⟨by
      simpa [horizontalStripLeftBlockScan] using
        firstClosedBlockScan_eq_of_agree (horizontalStripLeftCutBlock N n K)
          A B (List.range (N - K)) hAgreeL,
    by
      simpa [horizontalStripRightBlockScan] using
        firstClosedBlockScan_eq_of_agree (horizontalStripRightCutBlock N n K)
          A B (List.range (N - K)) hAgreeR⟩

/-- On a literal reveal record, both scan pairs agree with the representative
configuration, including success/failure and the chosen first-cut indices. -/
theorem horizontalStripClosedCutScans_eq_on_record
    (N n K : ℕ) (A A₀ : Finset (horizontalStripCutRectangle N n).edgeSet)
    (hKN : K ≤ N)
    (hrecord : A ∈ revealRecordEvent (horizontalStripCutRectangle N n)
      (horizontalStripClosedCutReveal N n K) A₀) :
    horizontalStripLeftBlockScan N n K A = horizontalStripLeftBlockScan N n K A₀ ∧
      horizontalStripRightBlockScan N n K A = horizontalStripRightBlockScan N n K A₀ := by
  exact horizontalStripClosedCutScans_eq_of_agree N n K A₀ A hKN hrecord.2

end
end PottsContinuity.FKC.Medial
