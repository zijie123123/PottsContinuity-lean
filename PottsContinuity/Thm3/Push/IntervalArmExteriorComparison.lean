module

public import PottsContinuity.Thm3.Push.IntervalArmJointRevealDisjoint
public import PottsContinuity.Thm3.Push.IntervalArmPhysicalSideIncidence
public import PottsContinuity.Thm3.Push.TwoRevealExteriorComparison
public import PottsContinuity.PlanarMixed.OmegaInterfaces

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12 PottsContinuity.PlanarMixed
noncomputable section
local instance armExteriorComparisonEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- The ACTUAL interval-arm exploration satisfies the reference-square
boundary comparison for EVERY exterior state. Both reveal separation and
physical-side label preservation are proved from the actual source events. -/
theorem intervalArmJoint_extremalBoundaryComparison
    (N : ℕ) (hN : 1 ≤ N) (l₁ r₁ l₂ r₂ : ℤ)
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
    ExtremalBoundaryComparison (0,0) N hN
      (activeUnexaminedGraph (rectangleGraph (0,0) N N) (L ∪ R))
      (Function.Embedding.subtype _)
      (twoRevealActiveBoundary (rectangleGraph (0,0) N N) L R hd) := by
  let G := rectangleGraph (0,0) N N
  let L := intervalArmFilledLeftReveal N l₁ r₁ A
  let R := intervalArmFilledRightReveal N l₂ r₂ A
  have hd := intervalArmJoint_reveal_vertices_disjoint N l₁ r₁ l₂ r₂
    hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno
  apply twoReveal_active_exterior_partitions_le_of_boundary_labels G L R hd
    (squareSeparateLeftRightBoundary (0,0) N hN)
  intro u v huv
  apply (twoArcAttachmentLabel_eq_iff _ _ hd u v).mpr
  rcases (twoBlockBoundary_partition_rel _ _ _ u v).mp huv with rfl | hs | hs
  · exact Or.inl rfl
  · right; left
    constructor
    · exact intervalArmFilledLeft_left_side_incident_reveal N l₁ r₁ hl₁ h₁ hr₁ A hA.1 u
        (by simpa only [Square.squareLeftArc,Set.mem_ofPred_eq] using hs.1)
    · exact intervalArmFilledLeft_left_side_incident_reveal N l₁ r₁ hl₁ h₁ hr₁ A hA.1 v
        (by simpa only [Square.squareLeftArc,Set.mem_ofPred_eq] using hs.2)
  · right; right
    constructor
    · exact intervalArmFilledRight_right_side_incident_reveal N l₂ r₂ hl₂ h₂ hr₂ A hA.2 u
        (by simpa only [Square.squareRightArc,Set.mem_ofPred_eq,zero_add] using hs.1)
    · exact intervalArmFilledRight_right_side_incident_reveal N l₂ r₂ hl₂ h₂ hr₂ A hA.2 v
        (by simpa only [Square.squareRightArc,Set.mem_ofPred_eq,zero_add] using hs.2)

end
end PottsContinuity.Push
