module

public import PottsContinuity.Thm3.Push.IntervalArmActiveFrozenBoundary

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12
noncomputable section
local instance armRemainingLowerEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- The genuine remaining FK law after the actual joint exploration has the
uniform attachment bound. It retains every original vertex and every original
boundary identification; only the active comparison omits isolated vertices. -/
theorem intervalArmJoint_remaining_attachment_lower_bound
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (hN : 1 ≤ N) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))
    (ξ : BoundaryCondition (RectangleVertex (0,0) N N)) :
    let G := rectangleGraph (0,0) N N
    let L := intervalArmFilledLeftReveal N l₁ r₁ A
    let R := intervalArmFilledRightReveal N l₂ r₂ A
    let Ω := activeUnexaminedGraph G (L ∪ R)
    1 / (1 + (q : ℝ)^2) ≤
      (measure (edgeRestriction G (L ∪ R)) (criticalParameters q) (frozenBoundary ξ (A ∩ (L ∪ R)))
        {D | embeddedConfigurationRestriction Ω (edgeRestriction G (L ∪ R))
          (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le_edgeRestriction G (L ∪ R)) D ∈
          arcsConnectionEvent Ω (twoRevealActiveLeftArc G L R) (twoRevealActiveRightArc G L R)}).toReal := by
  have hd := intervalArmJoint_reveal_vertices_disjoint N l₁ r₁ l₂ r₂
    hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno
  apply le_trans (intervalArmJoint_active_wiredArc_lower_bound q N hN l₁ r₁ l₂ r₂
    hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno)
  apply le_trans (measure_boundary_comparison (criticalParameters q) _ _
    (intervalArmJoint_active_boundary_le_frozen_record N l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ A hA hd ξ) _ (arcsConnectionEvent_isUpperSet _ _))
  exact RSW.embedded_boundary_probability_le _ _ (Function.Embedding.subtype _)
    (activeUnexaminedGraph_map_le_edgeRestriction _ _) (criticalParameters q)
    (frozenBoundary ξ (A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A)) _
    (arcsConnectionEvent_isUpperSet _ _)

end
end PottsContinuity.Push
