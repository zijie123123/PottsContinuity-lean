module

public import PottsContinuity.Thm3.Prop4.SplitSurgery
public import PottsContinuity.Thm3.Prop4.FiniteArmProduct
public import PottsContinuity.Thm3.Prop4.ArmSumShift

/-!
# Split-arm convolution from an actual separating screen

Four-edge surgery, simultaneous surviving arms and cluster factorization are
proved here. The remaining screen input is precisely geometric disconnection;
there is no assumed probability factorization or residual free-law assertion.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

noncomputable section
open PD.FK
attribute [local instance] configurationMeasurableSpace

local instance splitScreenEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- The true same-configuration disconnected arm union is bounded by the exact convolution. -/
theorem free_disconnected_arm_union_le_splitArmSum (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (n T : ℕ) (r : ℝ) (a b : (box n : Set (ℤ × ℤ))) :
    (measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅)
      {A | ¬ActualConnected _ A a b ∧ ∃ k l : ℕ, k+l=T ∧ r ≤ k ∧ r ≤ l ∧
        A ∈ finiteEndpointArmEvent n a k ∧ A ∈ finiteEndpointArmEvent n b l}).toReal ≤
      splitArmSum (RSW.oneArmProbability μ) r T := by
  classical
  let ν := measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅)
  let E : ℕ → Set (Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
    fun k => if r ≤ k ∧ r ≤ (T-k : ℕ) then
      {A | A ∈ finiteEndpointArmEvent n a k ∧ A ∈ finiteEndpointArmEvent n b (T-k) ∧
        ¬ActualConnected _ A a b} else ∅
  have hsub : {A | ¬ActualConnected _ A a b ∧ ∃ k l : ℕ, k+l=T ∧ r ≤ k ∧ r ≤ l ∧
        A ∈ finiteEndpointArmEvent n a k ∧ A ∈ finiteEndpointArmEvent n b l} ⊆
      ⋃ k ∈ Finset.range (T+1), E k := by
    rintro A ⟨hdisc,k,l,hkl,hk,hl,hak,hbl⟩
    have hl' : l=T-k := by omega
    refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
    dsimp [E]
    rw [ite_eq_left ⟨hk,by simpa only [← hl'] using hl⟩]
    exact ⟨hak,by simpa only [← hl'] using hbl,hdisc⟩
  calc
    _ ≤ ν.real (⋃ k ∈ Finset.range (T+1), E k) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range (T+1), ν.real (E k) := measureReal_biUnion_finset_le _ _
    _ ≤ splitArmSum (RSW.oneArmProbability μ) r T := by
      unfold splitArmSum
      apply Finset.sum_le_sum
      intro k _
      dsimp [E]
      split_ifs
      · exact free_disconnected_endpoint_arms_le_infinite_product θ μ hμ n a b k (T-k)
      · simp

/-- Equation-(29) surgery and product estimate, conditional only on the actual screen geometry. -/
theorem split_probability_le_arm_sum_of_separatingScreen (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (n : ℕ) (r : ℝ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : 2*⌈r⌉₊ ≤ 2*n-2)
    (a b z : (box n : Set (ℤ × ℤ)))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = (n : ℤ))
    (hfar : 4*r ≤ tubeDistance a.val b.val z.val)
    (B S : Set (Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))))
    (hS : IsLowerSet S)
    (hB : ∀ A ∈ B, A ∈ S ∧ ActualConnected _ A a z ∧ ActualConnected _ A b z)
    (hsep : ∀ C ∈ S,
      Disjoint C (vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z) →
        ¬ActualConnected _ C a b) :
    (1-edgeParameter θ)^4 *
      (measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅) B).toReal ≤
      splitArmSum (RSW.oneArmProbability μ) r (2*n-2) := by
  have hlower := split_star_arms_lower_of_lowerScreen θ n r hn hr hrn
    (BoundaryCondition.free ∅) a b z ha hb hfar B S hS hB
  apply hlower.trans
  apply le_trans _ (free_disconnected_arm_union_le_splitArmSum θ μ hμ n (2*n-2) r a b)
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro C ⟨hCS,hclosed,harms⟩
  exact ⟨hsep C hCS hclosed,harms⟩

end
end PottsContinuity.Thm3.Prop4
