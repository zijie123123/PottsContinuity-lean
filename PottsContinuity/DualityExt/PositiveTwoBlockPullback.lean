module

public import PottsContinuity.DualityExt.PositiveBoundaryMerge
public import PottsContinuity.DualityExt.PositiveConnectedBoundaryPartition
public import PottsContinuity.DualityExt.PositiveBoundaryReweighting
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.DualityExt.PositiveBoundaryMergeDualTransfer
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.DualityExt.PositiveSubgraphCrossingTransfer
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.DualityExt.PositiveBoundaryMergePDTransfer
public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import Mathlib.Tactic
public import Mathlib.Order.CompletePartialOrder

/-!
# Pullback of a separately wired boundary partition

The two-block partition is preserved by an injective carrier map when its
classes are replaced by their preimages.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

theorem positiveTwoBlockBoundary_rel_iff
    {V : Type*} (I O : Set V) (hIO : Disjoint I O) (x y : V) :
    (positiveTwoBlockBoundary I O hIO).partition.r x y ↔
      x = y ∨ (x ∈ I ∧ y ∈ I) ∨ (x ∈ O ∧ y ∈ O) := by
  let S : Setoid V := {
    r := fun x y => x = y ∨ (x ∈ I ∧ y ∈ I) ∨ (x ∈ O ∧ y ∈ O)
    iseqv := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact Or.inl rfl
      · intro x y h
        rcases h with h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
        · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · intro x y z hxy hyz
        rcases hxy with hxy | hxy | hxy
        · subst y
          exact hyz
        · rcases hyz with hyz | hyz | hyz
          · subst z
            exact Or.inr (Or.inl hxy)
          · exact Or.inr (Or.inl ⟨hxy.1, hyz.2⟩)
          · exact False.elim ((Set.disjoint_left.mp hIO) hxy.2 hyz.1)
        · rcases hyz with hyz | hyz | hyz
          · subst z
            exact Or.inr (Or.inr hxy)
          · exact False.elim ((Set.disjoint_left.mp hIO) hyz.1 hxy.2)
          · exact Or.inr (Or.inr ⟨hxy.1, hyz.2⟩) }
  have hsup :
      (BoundaryCondition.wired I).partition ⊔
        (BoundaryCondition.wired O).partition ≤ S := by
    apply sup_le
    · intro u v huv
      rcases (BoundaryCondition.wired_rel I u v).mp huv with heq | hI
      · exact Or.inl heq
      · exact Or.inr (Or.inl hI)
    · intro u v huv
      rcases (BoundaryCondition.wired_rel O u v).mp huv with heq | hO
      · exact Or.inl heq
      · exact Or.inr (Or.inr hO)
  have hle : S ≤
      (BoundaryCondition.wired I).partition ⊔
        (BoundaryCondition.wired O).partition := by
    intro u v huv
    rcases huv with heq | hI | hO
    · subst v
      exact Setoid.refl' _ u
    · have hIle : (BoundaryCondition.wired I).partition ≤
          (BoundaryCondition.wired I).partition ⊔
            (BoundaryCondition.wired O).partition := le_sup_left
      exact hIle ((BoundaryCondition.wired_rel I u v).2 (Or.inr hI))
    · have hOle : (BoundaryCondition.wired O).partition ≤
          (BoundaryCondition.wired I).partition ⊔
            (BoundaryCondition.wired O).partition := le_sup_right
      exact hOle ((BoundaryCondition.wired_rel O u v).2 (Or.inr hO))
  change ((BoundaryCondition.wired I).partition ⊔
    (BoundaryCondition.wired O).partition).r x y ↔ S.r x y
  rw [Setoid.eq_iff_rel_eq.mpr (le_antisymm hsup hle)]

theorem isolatedExtensionPullback_positiveTwoBlockBoundary_partition
    {V W : Type*} (f : V ↪ W) (I O : Set W)
    (hIO : Disjoint I O) :
    (isolatedExtensionPullbackBoundary f
      (positiveTwoBlockBoundary I O hIO)).partition =
    (positiveTwoBlockBoundary (f ⁻¹' I) (f ⁻¹' O)
      (by
        apply Set.disjoint_left.mpr
        intro x hxI hxO
        exact (Set.disjoint_left.mp hIO) hxI hxO)).partition := by
  apply Setoid.ext
  intro x y
  change (positiveTwoBlockBoundary I O hIO).partition.r (f x) (f y) ↔
    (positiveTwoBlockBoundary (f ⁻¹' I) (f ⁻¹' O) (by
      apply Set.disjoint_left.mpr
      intro z hzI hzO
      exact (Set.disjoint_left.mp hIO) hzI hzO)).partition.r x y
  rw [positiveTwoBlockBoundary_rel_iff, positiveTwoBlockBoundary_rel_iff]
  constructor
  · rintro (heq | hI | hO)
    · exact Or.inl (f.injective heq)
    · exact Or.inr (Or.inl (by simpa only [Set.mem_preimage] using hI))
    · exact Or.inr (Or.inr (by simpa only [Set.mem_preimage] using hO))
  · rintro (heq | hI | hO)
    · exact Or.inl (congrArg f heq)
    · exact Or.inr (Or.inl (by simpa only [Set.mem_preimage] using hI))
    · exact Or.inr (Or.inr (by simpa only [Set.mem_preimage] using hO))

end PottsContinuity.DualityExt
