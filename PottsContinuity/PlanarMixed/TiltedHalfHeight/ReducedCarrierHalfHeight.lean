module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.TopErasure
public import PottsContinuity.Thm3.RSW.TiltedStripReducedReads

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial
noncomputable section
attribute [local instance] Classical.propDecidable

theorem tiltedBondEdge_surjective (N : ℕ) (t : ℝ) :
    Function.Surjective (tiltedBondEdge N t) := by
  intro e
  let p := e.val.out
  have hp : s(p.1,p.2)=e.val := Quot.out_eq _
  have ha : (tiltedStripGraph N t).Adj p.1 p.2 :=
    (tiltedStripGraph N t).mem_edgeSet.mp (hp ▸ e.property)
  obtain ⟨b,hb,_⟩ := LatticeBond.existsUnique_of_adj
    (show squareLattice.Adj p.1.val p.2.val from ha)
  have he : (b.source=p.1.val ∧ b.target=p.2.val) ∨
      (b.source=p.2.val ∧ b.target=p.1.val) := Sym2.eq_iff.mp hb
  have hstrip : b.source∈tiltedStripVertices N t ∧ b.target∈tiltedStripVertices N t := by
    rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1 ▸ p.1.property,h2 ▸ p.2.property⟩
    · exact ⟨h1 ▸ p.2.property,h2 ▸ p.1.property⟩
  refine ⟨⟨b,hstrip⟩,?_⟩
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  change b.toSym2 = Sym2.map Subtype.val e.val
  rw [←hp,Sym2.map_mk]
  exact hb

/-- Canonical normalization of an actual original strip edge. -/
def normalizedStripEdge (N : ℕ) (t : ℝ) (e : (tiltedStripGraph N t).edgeSet) : TiltedBond N t :=
  (tiltedBondEdge_surjective N t e).choose

theorem normalizedStripEdge_eq (N : ℕ) (t : ℝ) (e : (tiltedStripGraph N t).edgeSet) :
    tiltedBondEdge N t (normalizedStripEdge N t e) = e :=
  (tiltedBondEdge_surjective N t e).choose_spec

/-- Lift the exact reduced labels of `RSW.tiltedStripReducedCarrier`, giving the deleted
wired edges state false. -/
def reducedCarrierLift (N : ℕ) (t : ℝ) (σ : RSW.tiltedStripReducedCarrier N t → Bool) :
    TiltedConfiguration N t :=
  fun e => if h : ¬ WiredTopEdge N t e then
    σ ⟨normalizedStripEdge N t e,by
      change ¬ WiredTopEdge N t (tiltedBondEdge N t (normalizedStripEdge N t e))
      rw [normalizedStripEdge_eq]
      exact h⟩ else false

theorem reducedCarrierLift_continuous (N : ℕ) (t : ℝ) : Continuous (reducedCarrierLift N t) := by
  apply continuous_pi
  intro e
  by_cases h : ¬ WiredTopEdge N t e
  · simpa only [reducedCarrierLift,dite_eq_left h] using
      (continuous_apply _ : Continuous (fun σ : RSW.tiltedStripReducedCarrier N t → Bool =>
        σ ⟨normalizedStripEdge N t e,by
          change ¬ WiredTopEdge N t (tiltedBondEdge N t (normalizedStripEdge N t e))
          rw [normalizedStripEdge_eq]
          exact h⟩))
  · simpa only [reducedCarrierLift,dite_eq_right h] using
      (continuous_const : Continuous (fun _ : RSW.tiltedStripReducedCarrier N t → Bool => false))

theorem reducedCarrierLift_restriction (N : ℕ) (t : ℝ) (ω : TiltedConfiguration N t) :
    reducedCarrierLift N t (RSW.tiltedStripReducedRestriction N t ω) = topErasedConfiguration N t ω := by
  funext e
  by_cases h : WiredTopEdge N t e
  · simp only [reducedCarrierLift,dite_eq_right (not_not_intro h),topErasedConfiguration,ite_eq_left h]
  · simp only [reducedCarrierLift,h,not_false_eq_true,dite_eq_left,RSW.tiltedStripReducedRestriction,
      normalizedStripEdge_eq,topErasedConfiguration,ite_false]

/-- A retained label is recovered literally by the canonical lift. -/
theorem reducedCarrierLift_at_label (N : ℕ) (t : ℝ)
    (σ : RSW.tiltedStripReducedCarrier N t → Bool) (b : RSW.tiltedStripReducedCarrier N t) :
    reducedCarrierLift N t σ (tiltedBondEdge N t b.val) = σ b := by
  have hn : ¬ WiredTopEdge N t (tiltedBondEdge N t b.val) := b.property
  have hb : normalizedStripEdge N t (tiltedBondEdge N t b.val) = b.val :=
    tiltedBondEdge_injective N t (normalizedStripEdge_eq N t _)
  simp only [reducedCarrierLift,dite_eq_left hn]
  congr 1
  exact Subtype.ext hb

/-- The native reduced dual state on a crossed image is the complementary
state of its original source bond. -/
theorem reducedLift_dual_at_image (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ω : TiltedConfiguration N t) (b : RSW.tiltedStripReducedCarrier N t) :
    reducedCarrierLift N t
        (RSW.tiltedStripReducedDualTransport N t ht (RSW.tiltedStripReducedRestriction N t ω))
        (tiltedBondEdge N t (RSW.tiltedStripReducedBondEquiv N t ht b).val) =
      !ω (tiltedBondEdge N t b.val) := by
  rw [reducedCarrierLift_at_label]
  simp only [RSW.tiltedStripReducedDualTransport,RSW.tiltedStripReducedRestriction]
  have hb : RSW.tiltedStripReducedBondEquiv N t ht
      (RSW.tiltedStripReducedBondEquiv N t ht b) = b :=
    (RSW.tiltedStripReducedBondEquiv N t ht).left_inv b
  rw [hb]

/-- The source event expressed directly on the reduced carrier
`RSW.tiltedStripReducedCarrier`. -/
def reducedCarrierHalfHeight (n : ℕ) (hn : 1 ≤ 2*n) (t : ℝ) :
    Set (RSW.tiltedStripReducedCarrier (2*n) t → Bool) :=
  {σ | lowestTopConnectedHeight (2*n) hn t (reducedCarrierLift (2*n) t σ) 0 ≤ n}

theorem halfHeight_reducedRestriction_preimage (n : ℕ) (hn : 1 ≤ 2*n) (t : ℝ) :
    (RSW.tiltedStripReducedRestriction (2*n) t) ⁻¹' reducedCarrierHalfHeight n hn t =
      {ω | lowestTopConnectedHeight (2*n) hn t ω 0 ≤ n} := by
  ext ω
  simp only [Set.mem_preimage,reducedCarrierHalfHeight,Set.mem_ofPred_eq,
    reducedCarrierLift_restriction,lowestHeight_topErased_eq]

theorem reducedCarrierHalfHeight_eq_iUnion (n : ℕ) (hn : 1 ≤ 2*n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    reducedCarrierHalfHeight n hn t = ⋃ R : ℕ, (reducedCarrierLift (2*n) t) ⁻¹'
      Thm3.Touch.tiltedTopConnectionWithinBox n R t := by
  change (reducedCarrierLift (2*n) t) ⁻¹'
    {ω | lowestTopConnectedHeight (2*n) hn t ω 0 ≤ n} = _
  rw [Thm3.Touch.lowestTopConnectedHeight_half_sublevel_eq_iUnion n hn t ht,Set.preimage_iUnion]

theorem reducedCarrier_bounded_paths_isClopen (n R : ℕ) (t : ℝ) :
    IsClopen ((reducedCarrierLift (2*n) t) ⁻¹' Thm3.Touch.tiltedTopConnectionWithinBox n R t) :=
  (Thm3.Touch.isClopen_tiltedTopConnectionWithinBox n R t).preimage
    (reducedCarrierLift_continuous (2*n) t)

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
