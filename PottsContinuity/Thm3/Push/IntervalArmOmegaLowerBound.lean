module

public import PottsContinuity.Thm3.Push.IntervalArmExteriorComparison
public import PottsContinuity.Thm3.Push.TwoRevealCrossingRestriction
public import PottsContinuity.PlanarMixed.OmegaConditional

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12 PottsContinuity.PlanarMixed
noncomputable section
local instance armOmegaLowerEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- Actual square crossings restrict to actual attachment connections in
the original interval exploration domain, with no assumed path surgery. -/
theorem intervalArmJoint_squareCrossingRestrictsToArcs
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂)) :
    let L := intervalArmFilledLeftReveal N l₁ r₁ A
    let R := intervalArmFilledRightReveal N l₂ r₂ A
    SquareCrossingRestrictsToArcs (0,0) N
      (activeUnexaminedGraph (rectangleGraph (0,0) N N) (L ∪ R))
      (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le _ _)
      (twoRevealActiveLeftArc _ L R) (twoRevealActiveRightArc _ L R) := by
  apply twoReveal_squareCrossingRestrictsToArcs (0,0) N _ _
    (intervalArmJoint_reveal_vertices_disjoint N l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno)
  · intro u hu
    exact intervalArmFilledLeft_left_side_incident_reveal N l₁ r₁ hl₁ h₁ hr₁ A hA.1 u
      (by simpa only [Square.squareLeftArc,Set.mem_ofPred_eq] using hu)
  · intro u hu
    exact intervalArmFilledRight_right_side_incident_reveal N l₂ r₂ hl₂ h₂ hr₂ A hA.2 u
      (by simpa only [Square.squareRightArc,Set.mem_ofPred_eq,zero_add] using hu)

/-- The actual active interval exploration domain has the mixed-square
lower bound for every real q at least one, at the explicit self-dual value.
No exploration geometry, boundary order, or numerical bound is a premise. -/
theorem intervalArmJoint_active_wiredArc_lower_bound
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (hN : 1 ≤ N) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂)) :
    let L := intervalArmFilledLeftReveal N l₁ r₁ A
    let R := intervalArmFilledRightReveal N l₂ r₂ A
    let hd := intervalArmJoint_reveal_vertices_disjoint N l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno
    1 / (1 + (q : ℝ)^2) ≤
      (measure (activeUnexaminedGraph (rectangleGraph (0,0) N N) (L ∪ R)) (criticalParameters q)
        (twoRevealActiveBoundary (rectangleGraph (0,0) N N) L R hd)
        (arcsConnectionEvent _ (twoRevealActiveLeftArc _ L R) (twoRevealActiveRightArc _ L R))).toReal := by
  apply omega_wiredArc_lower_bound_of_extremalBoundaryComparison q (0,0) N hN
    _ (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le _ _) _ _ _
  · exact intervalArmJoint_extremalBoundaryComparison N hN l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno
  · exact intervalArmJoint_squareCrossingRestrictsToArcs N l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno

end
end PottsContinuity.Push
