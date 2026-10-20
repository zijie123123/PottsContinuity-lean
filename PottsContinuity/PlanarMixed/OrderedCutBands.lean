module

public import PottsContinuity.PlanarMixed.OrderedCutRegions
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Star

/-!
# Constructing band labels from ordered cuts

Labels are the five exhaustive geometric classes: left accessible region (0),
first cut (1), the complement of both exterior regions and both cuts (2),
second cut (3), and right accessible region (4). The ordered-cut hypotheses
prove these classes disjoint. Label 2 is the stated complementary middle set,
not a replacement for a missing case. No label map is supplied by a consumer.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section

def orderedCutRank {V : Type*} (G : SimpleGraph V) (L R A C : Set V)
    (_h : OrderedCutPair G L R A C) (v : V) : ℤ := by
  classical
  exact if v ∈ cutReachRegion G A L then 0 else if v ∈ A then 1 else
    if v ∈ C then 3 else if v ∈ cutReachRegion G C R then 4 else 2

variable {V : Type*} {G : SimpleGraph V} {L R A C : Set V}
variable (h : OrderedCutPair G L R A C)

private theorem rank_left {v : V} (hv : v ∈ cutReachRegion G A L) :
    orderedCutRank G L R A C h v = 0 := by simp [orderedCutRank, hv]

private theorem rank_first {v : V} (hv : v ∈ A) : orderedCutRank G L R A C h v = 1 := by
  have hnot : v ∉ cutReachRegion G A L := fun hvL => cutReachRegion_avoids_cut hvL hv
  simp [orderedCutRank, hnot, hv]

private theorem rank_second {v : V} (hv : v ∈ C) : orderedCutRank G L R A C h v = 3 := by
  have hnotL : v ∉ cutReachRegion G A L := fun hvL => h.leftRegion_avoids_second hvL hv
  have hnotA : v ∉ A := fun hvA => Set.disjoint_left.mp h.disjoint hvA hv
  simp [orderedCutRank, hnotL, hnotA, hv]

private theorem rank_right {v : V} (hv : v ∈ cutReachRegion G C R) :
    orderedCutRank G L R A C h v = 4 := by
  have hnotL : v ∉ cutReachRegion G A L := fun hvL => Set.disjoint_left.mp h.regions_disjoint hvL hv
  have hnotA := h.rightRegion_avoids_first hv
  have hnotC := cutReachRegion_avoids_cut hv
  simp [orderedCutRank, hnotL, hnotA, hnotC, hv]

private theorem rank_middle {v : V} (hL : v ∉ cutReachRegion G A L)
    (hR : v ∉ cutReachRegion G C R) :
    1 ≤ orderedCutRank G L R A C h v ∧ orderedCutRank G L R A C h v ≤ 3 := by
  classical
  simp only [orderedCutRank, ite_eq_right hL, ite_eq_right hR]
  split_ifs <;> norm_num

/-- The constructed marked level is exactly the original first cut. -/
theorem orderedCutRank_eq_one_iff (v : V) : orderedCutRank G L R A C h v = 1 ↔ v ∈ A := by
  classical
  by_cases hv : v ∈ A
  · exact ⟨fun _ => hv, fun _ => rank_first h hv⟩
  · constructor
    · intro hr
      unfold orderedCutRank at hr
      simp only [ite_eq_right hv] at hr
      split_ifs at hr <;> norm_num at hr
    · exact fun ha => (hv ha).elim

/-- The constructed second marked level is exactly the original second cut. -/
theorem orderedCutRank_eq_three_iff (v : V) : orderedCutRank G L R A C h v = 3 ↔ v ∈ C := by
  classical
  by_cases hv : v ∈ C
  · exact ⟨fun _ => hv, fun _ => rank_second h hv⟩
  · constructor
    · intro hr
      unfold orderedCutRank at hr
      simp only [ite_eq_right hv] at hr
      split_ifs at hr <;> norm_num at hr
    · exact fun hc => (hv hc).elim

/-- All band edge conditions follow from ordinary cut separation. -/
theorem orderedCutRank_edges : RankedBandEdges G (orderedCutRank G L R A C h) := by
  classical
  intro u v huv
  by_cases huL : u ∈ cutReachRegion G A L
  · apply Or.inl
    constructor
    · rw [rank_left h huL]; norm_num
    · by_cases hvA : v ∈ A
      · rw [rank_first h hvA]
      · rw [rank_left h (cutReachRegion_edge_closed huL huv hvA)]; norm_num
  by_cases huR : u ∈ cutReachRegion G C R
  · apply Or.inr ∘ Or.inr
    constructor
    · rw [rank_right h huR]; norm_num
    · by_cases hvC : v ∈ C
      · rw [rank_second h hvC]
      · rw [rank_right h (cutReachRegion_edge_closed huR huv hvC)]; norm_num
  by_cases hvL : v ∈ cutReachRegion G A L
  · have huA : u ∈ A := by
      by_contra hn
      exact huL (cutReachRegion_edge_closed hvL huv.symm hn)
    exact Or.inl ⟨by rw [rank_first h huA], by rw [rank_left h hvL]; norm_num⟩
  by_cases hvR : v ∈ cutReachRegion G C R
  · have huC : u ∈ C := by
      by_contra hn
      exact huR (cutReachRegion_edge_closed hvR huv.symm hn)
    exact Or.inr (Or.inr
      ⟨by rw [rank_second h huC], by rw [rank_right h hvR]; norm_num⟩)
  exact Or.inr (Or.inl ⟨rank_middle h huL huR, rank_middle h hvL hvR⟩)

theorem orderedCutRank_left (v : V) (hv : v ∈ L) : orderedCutRank G L R A C h v ≤ 1 := by
  classical
  by_cases hvA : v ∈ A
  · rw [rank_first h hvA]
  · rw [rank_left h (cutReachRegion_contains G hv hvA)]; norm_num

theorem orderedCutRank_right (v : V) (hv : v ∈ R) : 3 ≤ orderedCutRank G L R A C h v := by
  classical
  by_cases hvC : v ∈ C
  · rw [rank_second h hvC]
  · rw [rank_right h (cutReachRegion_contains G hv hvC)]; norm_num

end
end PottsContinuity.PlanarMixed
