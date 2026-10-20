module

public import PottsContinuity.Thm3.Push.UpperBandTopBarrier
public import PottsContinuity.Thm3.Push.RectangleCutRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance bandRecordPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance bandRecordEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- On the upper-band crossing event, the canonical FULL-reference top
frontier already has an actual crossing inside the upper band. This avoids
any unnecessary assertion that the random lower domain contains a rectangle. -/
theorem upper_band_restricted_top_frontier_crosses (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H)
    (A₀ : Configuration (rectangleGraph a w H))
    (hband : DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A₀ ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t)) :
    DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht)
      (rectangleTopFrontier a w H A₀) ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t) := by
  let hrect := rectangle_upper_band_subset a w H t ht
  let hdual := rectangle_dual_upper_band_subset a w H t ht
  let ι := rectangleDualVertexEmbedding hdual
  let σ : RectangleDualVertex a w H → Bool := fun z => decide (z ∈ rectangleTopReached a w H A₀)
  change DualityExt.rectangleConfigurationRestriction hrect
    (auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w H) σ) ∈ _
  rw [← rectangle_labelCut_restriction hrect hdual σ]
  apply rectangle_dual_label_frontier_crosses
  · intro z hz
    apply decide_eq_false
    intro hS
    have hbound := rectangle_topReached_above_upper_band_bottom a w H t ht A₀ hband (ι z) hS
    have hzy : (ι z).val.2=a.2+(t : ℤ)-1 := by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      rfl
    omega
  · intro z hz
    apply decide_eq_true
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hport : ι (rectangleDualTopPortVertex (a.1,a.2+(t : ℤ)) w (H-t) i) =
        rectangleDualTopPortVertex a w H i := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (a.2+(t : ℤ))+((H-t : ℕ) : ℤ)=a.2+(H : ℤ)
        have hsub : ((H-t : ℕ) : ℤ)=(H : ℤ)-(t : ℤ) := Nat.cast_sub ht
        omega
    apply rectangleTopReached_top a w H A₀
    exact Finset.mem_image.mpr ⟨i,hi,hport.symm⟩

/-- The ACTUAL filled-exploration record certifies the upper-band crossing.
All states on that record, including its closed bonds, can be fixed before
applying the stopped FK law. No separate event-measurability premise remains. -/
theorem upper_band_crossing_on_filled_record (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H)
    (A₀ A : Configuration (rectangleGraph a w H))
    (hband : DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A₀ ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t))
    (hrecord : A ∩ rectangleFilledTopReveal a w H A₀ = A₀ ∩ rectangleFilledTopReveal a w H A₀) :
    DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t) := by
  have hfront : rectangleTopFrontier a w H A₀ ⊆ A := by
    intro f hf
    have hfr := rectangleTopFrontier_subset_open_and_revealed a w H A₀ hf
    have hfR := rectangleTopReveal_subset_filled a w H A₀ (Finset.mem_inter.mp hfr).2
    exact (Finset.mem_inter.mp (hrecord.symm ▸
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hfr).1,hfR⟩))).1
  obtain ⟨u,v,hu,hv,hconn⟩ := upper_band_restricted_top_frontier_crosses a w H t ht A₀ hband
  exact ⟨u,v,hu,hv,actualConnected_mono
    (embeddedConfigurationRestriction_monotone _ _ _ _ hfront) hconn⟩

end
end PottsContinuity.Push
