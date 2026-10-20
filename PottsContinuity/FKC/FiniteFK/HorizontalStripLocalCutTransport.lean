-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalCutTransport.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutFailure
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleConfiguration
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightLocalization
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripLocalCutTransportEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance horizontalStripLocalCutTransportEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

theorem horizontalStripLocalLeftCutScan_none_iff_every_candidate_meets_open
    (N n M : ℕ) (_hMN : M ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    (horizontalStripLocalLeftCutScan N n M A).2 = none ↔
      ∀ i, i < M → ∃ e, e ∈ horizontalStripLocalLeftCutBlock N n M i ∧ e ∈ A := by
  rw [horizontalStripLocalLeftCutScan, firstClosedBlockScan_none_iff]
  constructor
  · intro h i hi
    have h' := h i (List.mem_range.mpr hi)
    rw [Finset.not_disjoint_iff_nonempty_inter] at h'
    rcases h' with ⟨e, he⟩
    have he' : e ∈ A ∩ horizontalStripLocalLeftCutBlock N n M i := he
    rw [Finset.mem_inter] at he'
    exact ⟨e, he'.2, he'.1⟩
  · intro h i hi
    have hi' : i < M := List.mem_range.mp hi
    have ⟨e, heB, heA⟩ := h i hi'
    rw [Finset.not_disjoint_iff_nonempty_inter]
    exact ⟨e, Finset.mem_inter.mpr ⟨heA, heB⟩⟩

theorem horizontalStripLocalRightCutScan_none_iff_every_candidate_meets_open
    (N n M : ℕ) (_hMN : M ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    (horizontalStripLocalRightCutScan N n M A).2 = none ↔
      ∀ i, i < M → ∃ e, e ∈ horizontalStripLocalRightCutBlock N n M i ∧ e ∈ A := by
  rw [horizontalStripLocalRightCutScan, firstClosedBlockScan_none_iff]
  constructor
  · intro h i hi
    have h' := h i (List.mem_range.mpr hi)
    rw [Finset.not_disjoint_iff_nonempty_inter] at h'
    rcases h' with ⟨e, he⟩
    have he' : e ∈ A ∩ horizontalStripLocalRightCutBlock N n M i := he
    rw [Finset.mem_inter] at he'
    exact ⟨e, he'.2, he'.1⟩
  · intro h i hi
    have hi' : i < M := List.mem_range.mp hi
    have ⟨e, heB, heA⟩ := h i hi'
    rw [Finset.not_disjoint_iff_nonempty_inter]
    exact ⟨e, Finset.mem_inter.mpr ⟨heA, heB⟩⟩

theorem horizontalStripLocalLeftCutScan_none_iff_no_closed_candidate
    (N n M : ℕ) (hMN : M ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    (horizontalStripLocalLeftCutScan N n M A).2 = none ↔
      ¬ ∃ i, i < M ∧ ∀ e ∈ horizontalStripLocalLeftCutBlock N n M i, e ∉ A := by
  rw [horizontalStripLocalLeftCutScan_none_iff_every_candidate_meets_open N n M hMN A]
  constructor
  · intro h ⟨i, hi, hclosed⟩
    obtain ⟨e, heB, heA⟩ := h i hi
    exact hclosed e heB heA
  · intro h i hi
    by_contra hno
    apply h
    refine ⟨i, hi, ?_⟩
    intro e heB heA
    exact hno ⟨e, heB, heA⟩

theorem horizontalStripLocalRightCutScan_none_iff_no_closed_candidate
    (N n M : ℕ) (hMN : M ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    (horizontalStripLocalRightCutScan N n M A).2 = none ↔
      ¬ ∃ i, i < M ∧ ∀ e ∈ horizontalStripLocalRightCutBlock N n M i, e ∉ A := by
  rw [horizontalStripLocalRightCutScan_none_iff_every_candidate_meets_open N n M hMN A]
  constructor
  · intro h ⟨i, hi, hclosed⟩
    obtain ⟨e, heB, heA⟩ := h i hi
    exact hclosed e heB heA
  · intro h i hi
    by_contra hno
    apply h
    refine ⟨i, hi, ?_⟩
    intro e heB heA
    exact hno ⟨e, heB, heA⟩

private theorem horizontalStripLocalLeftCutBlock_image
    (N n M : ℕ) (hMN : M ≤ N) {i : ℕ} (hi : i < M) :
    (horizontalStripLocalLeftCutBlock N n M i).image
      (horizontalStripRectangleOriginalEdge N n) =
        horizontalStripCutEdges n (-(M : ℤ) + (i : ℤ)) := by
  have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
  have hleft : -(N : ℤ) ≤ -(M : ℤ) + (i : ℤ) := by omega
  have hright : -(M : ℤ) + (i : ℤ) < N := by omega
  simpa [horizontalStripLocalLeftCutBlock, hMN, hi] using
    horizontalStripRectangleCutEdges_original_image N n _ hleft hright

private theorem horizontalStripLocalRightCutBlock_image
    (N n M : ℕ) (hMN : M ≤ N) {i : ℕ} (hi : i < M) :
    (horizontalStripLocalRightCutBlock N n M i).image
      (horizontalStripRectangleOriginalEdge N n) =
        horizontalStripCutEdges n ((M : ℤ) - 1 - (i : ℤ)) := by
  have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
  have hleft : -(N : ℤ) ≤ (M : ℤ) - 1 - (i : ℤ) := by omega
  have hright : (M : ℤ) - 1 - (i : ℤ) < N := by omega
  simpa [horizontalStripLocalRightCutBlock, hMN, hi] using
    horizontalStripRectangleCutEdges_original_image N n _ hleft hright

theorem horizontalStripLocalLeftCutExists_iff_closed_extension
    (N n M : ℕ) (hMN : M ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    (∃ k : ℤ, -(M : ℤ) ≤ k ∧ k < 0 ∧
      ∀ e ∈ horizontalStripCutEdges n k,
        horizontalStripRectanglePlaneExtension N n A e = false) ↔
    (∃ i : ℕ, i < M ∧
      ∀ e ∈ horizontalStripLocalLeftCutBlock N n M i, e ∉ A) := by
  constructor
  · rintro ⟨k, hklo, hkhi, hclosed⟩
    let i : ℕ := (k + M).toNat
    have hk : 0 ≤ k + (M : ℤ) := by omega
    have hcast : (i : ℤ) = k + M := by
      dsimp [i]
      exact Int.toNat_of_nonneg hk
    have hi : i < M := by
      have : ((k + M).toNat : ℤ) < (M : ℤ) := by omega
      exact_mod_cast this
    refine ⟨i, hi, ?_⟩
    intro e he hfA
    have he' : horizontalStripRectangleOriginalEdge N n e ∈
        (horizontalStripLocalLeftCutBlock N n M i).image
          (horizontalStripRectangleOriginalEdge N n) := Finset.mem_image.mpr ⟨e, he, rfl⟩
    rw [horizontalStripLocalLeftCutBlock_image N n M hMN hi] at he'
    have hcol : -(M : ℤ) + (i : ℤ) = k := by omega
    have he'' : horizontalStripRectangleOriginalEdge N n e ∈
        horizontalStripCutEdges n k := by simpa [hcol] using he'
    have hfalse := hclosed (horizontalStripRectangleOriginalEdge N n e) he''
    have htrue := (horizontalStripRectanglePlaneExtension_mem_originalEdge N n A e).mpr hfA
    rw [hfalse] at htrue
    contradiction
  · rintro ⟨i, hi, hclosed⟩
    refine ⟨-(M : ℤ) + (i : ℤ), by omega, by omega, ?_⟩
    intro e he
    have himage := horizontalStripLocalLeftCutBlock_image N n M hMN hi
    have he' : e ∈ (horizontalStripLocalLeftCutBlock N n M i).image
        (horizontalStripRectangleOriginalEdge N n) := by
      rw [himage]
      exact he
    rcases Finset.mem_image.mp he' with ⟨f, hf, hfe⟩
    have hfa : f ∉ A := hclosed f hf
    have hfalse : horizontalStripRectanglePlaneExtension N n A
        (horizontalStripRectangleOriginalEdge N n f) = false := by
      have hnot : horizontalStripRectanglePlaneExtension N n A
          (horizontalStripRectangleOriginalEdge N n f) ≠ true := by
        intro htrue
        exact hfa ((horizontalStripRectanglePlaneExtension_mem_originalEdge N n A f).mp htrue)
      exact Bool.eq_false_of_not_eq_true hnot
    rw [hfe] at hfalse
    exact hfalse

theorem horizontalStripLocalRightCutExists_iff_closed_extension
    (N n M : ℕ) (hMN : M ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    (∃ k : ℤ, 0 ≤ k ∧ k < M ∧
      ∀ e ∈ horizontalStripCutEdges n k,
        horizontalStripRectanglePlaneExtension N n A e = false) ↔
    (∃ i : ℕ, i < M ∧
      ∀ e ∈ horizontalStripLocalRightCutBlock N n M i, e ∉ A) := by
  constructor
  · rintro ⟨k, hklo, hkhi, hclosed⟩
    let i : ℕ := ((M : ℤ) - 1 - k).toNat
    have hk : 0 ≤ (M : ℤ) - 1 - k := by omega
    have hcast : (i : ℤ) = (M : ℤ) - 1 - k := by
      dsimp [i]
      exact Int.toNat_of_nonneg hk
    have hi : i < M := by
      have hlt : (((M : ℤ) - 1 - k).toNat : ℤ) < (M : ℤ) := by
        rw [Int.toNat_of_nonneg hk]
        omega
      exact_mod_cast hlt
    refine ⟨i, hi, ?_⟩
    intro e he hfA
    have he' : horizontalStripRectangleOriginalEdge N n e ∈
        (horizontalStripLocalRightCutBlock N n M i).image
          (horizontalStripRectangleOriginalEdge N n) := Finset.mem_image.mpr ⟨e, he, rfl⟩
    rw [horizontalStripLocalRightCutBlock_image N n M hMN hi] at he'
    have hcol : (M : ℤ) - 1 - (i : ℤ) = k := by omega
    have he'' : horizontalStripRectangleOriginalEdge N n e ∈
        horizontalStripCutEdges n k := by simpa [hcol] using he'
    have hfalse := hclosed (horizontalStripRectangleOriginalEdge N n e) he''
    have htrue := (horizontalStripRectanglePlaneExtension_mem_originalEdge N n A e).mpr hfA
    rw [hfalse] at htrue
    contradiction
  · rintro ⟨i, hi, hclosed⟩
    refine ⟨(M : ℤ) - 1 - (i : ℤ), by omega, by omega, ?_⟩
    intro e he
    have himage := horizontalStripLocalRightCutBlock_image N n M hMN hi
    have he' : e ∈ (horizontalStripLocalRightCutBlock N n M i).image
        (horizontalStripRectangleOriginalEdge N n) := by
      rw [himage]
      exact he
    rcases Finset.mem_image.mp he' with ⟨f, hf, hfe⟩
    have hfa : f ∉ A := hclosed f hf
    have hnot : horizontalStripRectanglePlaneExtension N n A
        (horizontalStripRectangleOriginalEdge N n f) ≠ true := by
      intro htrue
      exact hfa ((horizontalStripRectanglePlaneExtension_mem_originalEdge N n A f).mp htrue)
    have hfalse := Bool.eq_false_of_not_eq_true hnot
    rw [hfe] at hfalse
    exact hfalse

theorem horizontalStripLocalClosedCutSuccess_closedExtension_preimage_iff
    (N n M : ℕ) (hMN : M ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    horizontalStripRectanglePlaneExtension N n A ∈ horizontalStripLocalClosedCutSuccess M n ↔
      A ∉ horizontalStripLocalCutFailureEvent N n M := by
  classical
  change (∃ l : ℤ, -(M : ℤ) ≤ l ∧ l < 0 ∧
      ∃ r : ℤ, 0 ≤ r ∧ r < (M : ℤ) ∧
        (∀ e ∈ horizontalStripCutEdges n l,
          horizontalStripRectanglePlaneExtension N n A e = false) ∧
        ∀ e ∈ horizontalStripCutEdges n r,
          horizontalStripRectanglePlaneExtension N n A e = false) ↔
      ¬ ((horizontalStripLocalLeftCutScan N n M A).2 = none ∨
        (horizontalStripLocalRightCutScan N n M A).2 = none)
  simp only [not_or]
  have hL := horizontalStripLocalLeftCutScan_none_iff_no_closed_candidate N n M hMN A
  have hR := horizontalStripLocalRightCutScan_none_iff_no_closed_candidate N n M hMN A
  constructor
  · rintro ⟨l, hlower, hleft, r, hright, hupper, hclosedL, hclosedR⟩
    have hfiniteL := (horizontalStripLocalLeftCutExists_iff_closed_extension
      N n M hMN A).mp ⟨l, hlower, hleft, hclosedL⟩
    have hfiniteR := (horizontalStripLocalRightCutExists_iff_closed_extension
      N n M hMN A).mp ⟨r, hright, hupper, hclosedR⟩
    constructor
    · intro hnone
      exact hL.mp hnone hfiniteL
    · intro hnone
      exact hR.mp hnone hfiniteR
  · intro hscan
    have hfiniteL : ∃ i, i < M ∧
        ∀ e ∈ horizontalStripLocalLeftCutBlock N n M i, e ∉ A := by
      by_contra hno
      exact hscan.1 (hL.mpr hno)
    have hfiniteR : ∃ i, i < M ∧
        ∀ e ∈ horizontalStripLocalRightCutBlock N n M i, e ∉ A := by
      by_contra hno
      exact hscan.2 (hR.mpr hno)
    obtain ⟨l, hlower, hleft, hclosedL⟩ :=
      (horizontalStripLocalLeftCutExists_iff_closed_extension N n M hMN A).mpr hfiniteL
    obtain ⟨r, hright, hupper, hclosedR⟩ :=
      (horizontalStripLocalRightCutExists_iff_closed_extension N n M hMN A).mpr hfiniteR
    exact ⟨l, hlower, hleft, r, hright, hupper, hclosedL, hclosedR⟩

end
end PottsContinuity.FKC.Medial
