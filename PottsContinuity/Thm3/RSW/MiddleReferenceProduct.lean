module

public import PottsContinuity.Thm3.RSW.FrozenTwoReferenceProduct
public import PottsContinuity.Thm3.RSW.StoppingJointAverage

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance middleReferenceEdgeEq {Y : Type*} (H : SimpleGraph Y) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Averaging exact middle fibres yields the joint lower product on every
event visible in those recorded sampled bonds. Both reference-law comparisons
come from residual graph geometry, and all original events are retained. -/
theorem middle_visible_joint_lower_of_closedInteriors
    {Y : Type*} [Finite Y] (H : SimpleGraph Y) (θ : Parameters)
    (ξ : BoundaryCondition Y) (R : Configuration H)
    (D : Set Y)
    (hR : ∀ ⦃e : H.edgeSet⦄, e ∈ R → ∀ ⦃v : Y⦄, v ∈ e.val → v ∈ D)
    (X : Fin 2 → Type*) [hX : ∀ i, Finite (X i)]
    (G : (i : Fin 2) → SimpleGraph (X i)) (f : (i : Fin 2) → X i ↪ Y)
    (hGH : ∀ i, (G i).map (f i) ≤ edgeRestriction H R)
    (B : (i : Fin 2) → Set (X i))
    (hclosed : ∀ i, ∀ ⦃x : X i⦄, x ∉ B i → ∀ ⦃y : Y⦄,
      (edgeRestriction H R).Adj (f i x) y → ∃ z : X i, f i z = y ∧ (G i).Adj x z)
    (havoid : ∀ i, ∀ ⦃x : X i⦄, x ∉ B i → f i x ∉ ξ.boundary ∪ D)
    (S : (i : Fin 2) → Set (Configuration (G i))) (hS : ∀ i, IsLowerSet (S i))
    (E : Fin 2 → Set (Configuration H)) (hE : ∀ i, IsLowerSet (E i))
    (hevent : ∀ K : RemovedConfiguration H R, ∀ i, ∀ A : Configuration (edgeRestriction H R),
      (edgeRestrictionConfigurationEquiv H R A).val ∪ K.val ∈ E i ↔
        embeddedConfigurationRestriction (G i) (edgeRestriction H R) (f i) (hGH i) A ∈ S i)
    (L : Set (Configuration H))
    (hvisible : ∀ C C', C ∩ R = C' ∩ R → (C ∈ L ↔ C' ∈ L)) :
    (measure (G 0) θ (BoundaryCondition.wired (B 0)) (S 0)).toReal *
      (measure (G 1) θ (BoundaryCondition.wired (B 1)) (S 1)).toReal *
      (measure H θ ξ L).toReal ≤
      (measure H θ ξ ((E 0 ∩ E 1) ∩ L)).toReal := by
  let reveal : RevealMap (G := H) := fun _ => R
  have hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C := by
    intro C C' _
    rfl
  let T : Set (StoppingObservationRange reveal) := (stoppingObservationMap reveal) '' L
  have hselect : (stoppingObservationMap reveal) ⁻¹' T = L := by
    ext C
    constructor
    · rintro ⟨C',hC',heq⟩
      have hstate : C' ∩ R = C ∩ R := congrArg (fun b => b.val.2) heq
      exact (hvisible C' C hstate).mp hC'
    · intro hC
      exact ⟨C,hC,rfl⟩
  have h := stopped_joint_event_lower_of_record_bounds θ ξ reveal hstable
    (E 0 ∩ E 1) T
    ((measure (G 0) θ (BoundaryCondition.wired (B 0)) (S 0)).toReal *
      (measure (G 1) θ (BoundaryCondition.wired (B 1)) (S 1)).toReal) (by
        intro C₀ _
        let K := revealRecordConfiguration reveal C₀
        have hbound := frozen_two_reference_product_lower_of_closedInteriors H θ ξ R K D
          (fun e he v hv => hR (K.property he) hv) X G f hGH B hclosed havoid S hS E hE
          (hevent K)
        have hrec : revealRecordEvent reveal C₀ = frozenStateEvent R K :=
          revealRecordEvent_eq_frozenStateEvent reveal hstable C₀
        have hfilter : (law H θ ξ).filter (revealRecordEvent reveal C₀)
            (by rw [hrec]; exact frozenStateEvent_support θ ξ R K) =
          (law H θ ξ).filter (frozenStateEvent R K) (frozenStateEvent_support θ ξ R K) := by
          ext A
          simp only [PMF.filter_apply,hrec]
        rw [hfilter]
        exact hbound)
  rw [hselect] at h
  exact h

end
end PottsContinuity.RSW
