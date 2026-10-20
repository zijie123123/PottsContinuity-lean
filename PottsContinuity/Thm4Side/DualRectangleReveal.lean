module

public import PottsContinuity.Thm4Side.ScreenSideSelection

@[expose] public section

namespace PottsContinuity.Thm4Side

open PottsContinuity.Exploration
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.RSW
open PottsContinuity.Thm4Plane

noncomputable section

local instance sideDualRevealEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

local instance sideDualRevealEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

/-- The right deterministic reveal of everything strictly left of the cut.
Vertical bonds on the cut and bonds to its right remain residual. -/
noncomputable def slitRightDualRectangleRevealEdges (m : ℕ) :
    Configuration (slitBoxGraph (16 * m)) := by
  exact slitRightHalfRevealEdges m

noncomputable def slitRightDualRectangleReveal (m : ℕ) :
    RevealMap (G := slitBoxGraph (16 * m)) :=
  fun _ => slitRightDualRectangleRevealEdges m

/-- The screen event remains determined by the augmented right reveal. -/
theorem slitScreenEvent_rightDualRectangleReveal_invariant (m : ℕ)
    (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitRightDualRectangleRevealEdges m =
      A ∩ slitRightDualRectangleRevealEdges m) :
    (A ∈ slitScreenEvent m ↔ B ∈ slitScreenEvent m) := by
  exact slitScreenEvent_rightReveal_invariant m A B hagree

/-- The reflected deterministic reveal of the right side of the mirror cut.
Its cut line and right region are conditioned, leaving the left half-domain
as the residual carrier. -/
noncomputable def slitLeftDualRectangleRevealEdges (m : ℕ) :
    Configuration (slitBoxGraph (16 * m)) := by
  exact slitLeftHalfRevealEdges m

noncomputable def slitLeftDualRectangleReveal (m : ℕ) :
    RevealMap (G := slitBoxGraph (16 * m)) :=
  fun _ => slitLeftDualRectangleRevealEdges m

theorem slitScreenEvent_leftDualRectangleReveal_invariant (m : ℕ)
    (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitLeftDualRectangleRevealEdges m =
      A ∩ slitLeftDualRectangleRevealEdges m) :
    (A ∈ slitScreenEvent m ↔ B ∈ slitScreenEvent m) := by
  exact slitScreenEvent_leftReveal_invariant m A B hagree

theorem slitScreenRightCrossingEvent_leftDualRectangleReveal_invariant
    (m : ℕ) (hm : 1 ≤ m) (A B : Configuration (slitBoxGraph (16 * m)))
    (hagree : B ∩ slitLeftDualRectangleRevealEdges m =
      A ∩ slitLeftDualRectangleRevealEdges m) :
    (A ∈ slitScreenRightCrossingEvent m ↔
      B ∈ slitScreenRightCrossingEvent m) := by
  exact slitScreenRightCrossingEvent_leftReveal_invariant m hm A B hagree

end
end PottsContinuity.Thm4Side
