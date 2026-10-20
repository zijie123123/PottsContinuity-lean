module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.FixedRevealAverage
public import PottsContinuity.Thm4Plane.ScreenFactorAssembly
public import PottsContinuity.Thm4Side.DualRectangleReveal
public import PottsContinuity.Thm3.Push.UnconditionalPush

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open MeasureTheory PD.FK Thm4Plane Thm4Side RSW
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance directSideAverageEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

def slitRightResidualCrossingProbability (q : Set.Icc (1 : ℝ) 4) (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) : ℝ :=
  ((remainingLaw (FKC.FiniteFK.slitBoxGraph (16*m))
      (criticalParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ)))
      (frozenBoundary (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m)))
        (A ∩ slitRightDualRectangleRevealEdges m))
      (slitRightDualRectangleRevealEdges m)).toMeasure
    {D | D.val ∪ (A ∩ slitRightDualRectangleRevealEdges m) ∈
      FKC.FiniteFK.slitScreenRightCrossingEvent m}).toReal

def slitLeftResidualCrossingProbability (q : Set.Icc (1 : ℝ) 4) (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) : ℝ :=
  ((remainingLaw (FKC.FiniteFK.slitBoxGraph (16*m))
      (criticalParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ)))
      (frozenBoundary (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m)))
        (A ∩ slitLeftDualRectangleRevealEdges m))
      (slitLeftDualRectangleRevealEdges m)).toMeasure
    {D | D.val ∪ (A ∩ slitLeftDualRectangleRevealEdges m) ∈
      FKC.FiniteFK.slitScreenLeftCrossingEvent m}).toReal

theorem slitScreen_right_factor_of_residual_bounds
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) (c : ℝ)
    (hbound : ∀ A ∈ slitScreenEvent m,
      c ≤ slitRightResidualCrossingProbability q m A) :
    c * (slitScreenFiniteMeasure q m).real (slitScreenEvent m) ≤
      (slitScreenFiniteMeasure q m).real
        (slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m) := by
  have h := fixedReveal_joint_lower_of_remaining_bounds
    (criticalParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ)))
    (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m)))
    (slitRightDualRectangleRevealEdges m) (slitScreenEvent m)
    (FKC.FiniteFK.slitScreenRightCrossingEvent m) c
    (slitScreenEvent_rightDualRectangleReveal_invariant m) hbound
  exact h

theorem slitScreen_left_factor_of_residual_bounds
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) (hm : 1 ≤ m) (c : ℝ)
    (hbound : ∀ A ∈ slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m,
      c ≤ slitLeftResidualCrossingProbability q m A) :
    c * (slitScreenFiniteMeasure q m).real
      (slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m) ≤
    (slitScreenFiniteMeasure q m).real
      (slitScreenEvent m ∩
        (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
          FKC.FiniteFK.slitScreenRightCrossingEvent m)) := by
  have hinv : ∀ A B : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)),
      B ∩ slitLeftDualRectangleRevealEdges m = A ∩ slitLeftDualRectangleRevealEdges m →
      (A ∈ slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m ↔
        B ∈ slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m) := by
    intro A B hab
    exact and_congr (slitScreenEvent_leftDualRectangleReveal_invariant m A B hab)
      (slitScreenRightCrossingEvent_leftDualRectangleReveal_invariant m hm A B hab)
  have h := fixedReveal_joint_lower_of_remaining_bounds
    (criticalParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ)))
    (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m)))
    (slitLeftDualRectangleRevealEdges m)
    (slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m)
    (FKC.FiniteFK.slitScreenLeftCrossingEvent m) c hinv hbound
  have heq : (slitScreenEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m) ∩
      FKC.FiniteFK.slitScreenLeftCrossingEvent m = slitScreenEvent m ∩
        (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩ FKC.FiniteFK.slitScreenRightCrossingEvent m) := by
    ext A
    simp only [Set.mem_inter_iff]
    tauto
  rw [heq] at h
  exact h

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
