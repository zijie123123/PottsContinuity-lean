module

public import PottsContinuity.Thm3.Push.IntervalArmOmegaLowerBound
public import PottsContinuity.PlanarMixed.EmbeddedActiveLaw

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PlanarMixed
noncomputable section
local instance armActiveFrozenEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- The two minimal active attachment classes are genuinely wired by the
actual OPEN joint record, for EVERY original boundary. Disjointness is the
already-proved geometric input selecting the two-class minimal boundary. -/
theorem intervalArmJoint_active_boundary_le_frozen_record
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hd : Disjoint
      (revealIncidentVertices (rectangleGraph (0,0) N N) (intervalArmFilledLeftReveal N l₁ r₁ A))
      (revealIncidentVertices (rectangleGraph (0,0) N N) (intervalArmFilledRightReveal N l₂ r₂ A)))
    (ξ : BoundaryCondition (RectangleVertex (0,0) N N)) :
    let L := intervalArmFilledLeftReveal N l₁ r₁ A
    let R := intervalArmFilledRightReveal N l₂ r₂ A
    (twoRevealActiveBoundary (rectangleGraph (0,0) N N) L R hd).partition ≤
      (isolatedExtensionPullbackBoundary (Function.Embedding.subtype _)
        (frozenBoundary ξ (A ∩ (L ∪ R)))).partition := by
  let G := rectangleGraph (0,0) N N
  let L := intervalArmFilledLeftReveal N l₁ r₁ A
  let R := intervalArmFilledRightReveal N l₂ r₂ A
  have hL : intervalArmFilledLeftFrontier N l₁ r₁ A ⊆ A ∩ (L ∪ R) :=
    ((intervalArmFilledLeftFrontier_subset_open_raw_record N l₁ r₁ A).trans
      (Finset.inter_subset_inter_left (intervalArmLeftReveal_subset_filled N l₁ r₁ A))).trans
      (Finset.inter_subset_inter_left Finset.subset_union_left)
  have hR : intervalArmFilledRightFrontier N l₂ r₂ A ⊆ A ∩ (L ∪ R) :=
    (intervalArmFilledRightFrontier_subset_open_record N l₂ r₂ A).trans
      (Finset.inter_subset_inter_left Finset.subset_union_right)
  apply twoBlockBoundary_le_pullback_frozen_of_arcConnections G (Function.Embedding.subtype _)
    ξ (A ∩ (L ∪ R)) _ _ (hd.preimage Subtype.val)
  · intro u hu v hv
    apply actualConnected_mono hL
    exact intervalArmFilled_attachment_vertices_connected N l₁ r₁ hl₁ h₁ hr₁ A hA.1 u.val v.val
      (twoRevealActiveLeftArc_mixed G L R u hu) (twoRevealActiveLeftArc_mixed G L R v hv)
  · intro u hu v hv
    apply actualConnected_mono hR
    exact intervalArmFilledRight_attachment_vertices_connected N l₂ r₂ hl₂ h₂ hr₂ A hA.2 u.val v.val
      (twoRevealActiveRightArc_mixed G L R u hu) (twoRevealActiveRightArc_mixed G L R v hv)

end
end PottsContinuity.Push
