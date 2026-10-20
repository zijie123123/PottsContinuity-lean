/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/TwoBlockBoundaryMerge.lean`.
Adaptation: namespace BD12, reuse PD.FK, all real q >= 1 and independent p.
The unrelated rectangle-collar import is replaced by the existing general
boundary-partition law lemma. Boundary merge is the BD12-local boundaryMerge.
-/
module

public import PottsContinuity.BD12.BoundaryMergeComparison
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK

noncomputable section

variable {V : Type*} [Finite V]

/-- The explicit relation for two disjoint wired blocks: each block is wired
internally and all vertices outside their union are singletons. -/
def twoBlockSetoid (A B : Set V) (hAB : Disjoint A B) : Setoid V where
  r x y := x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)
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
        · exact False.elim ((Set.disjoint_left.mp hAB) hxy.2 hyz.1)
      · rcases hyz with hyz | hyz | hyz
        · subst z
          exact Or.inr (Or.inr hxy)
        · exact False.elim ((Set.disjoint_left.mp hAB) hyz.1 hxy.2)
        · exact Or.inr (Or.inr ⟨hxy.1, hyz.2⟩)

omit [Finite V] in
theorem twoBlockSetoid_eq_sup (A B : Set V) (hAB : Disjoint A B) :
    twoBlockSetoid A B hAB =
      (BoundaryCondition.wired A).partition ⊔
        (BoundaryCondition.wired B).partition := by
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    rcases h with h | h | h
    · subst y
      exact ((BoundaryCondition.wired A).partition ⊔
        (BoundaryCondition.wired B).partition).refl x
    · exact (le_sup_left : (BoundaryCondition.wired A).partition ≤ _)
        ((BoundaryCondition.wired_rel A x y).mpr (Or.inr h))
    · exact (le_sup_right : (BoundaryCondition.wired B).partition ≤ _)
        ((BoundaryCondition.wired_rel B x y).mpr (Or.inr h))
  · intro h
    have hA : (BoundaryCondition.wired A).partition ≤ twoBlockSetoid A B hAB := by
      intro a b hab
      rcases (BoundaryCondition.wired_rel A a b).mp hab with hab | hab
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
    have hB : (BoundaryCondition.wired B).partition ≤ twoBlockSetoid A B hAB := by
      intro a b hab
      rcases (BoundaryCondition.wired_rel B a b).mp hab with hab | hab
      · exact Or.inl hab
      · exact Or.inr (Or.inr hab)
    exact (sup_le hA hB) h

/-- A boundary with two disjoint, separately wired blocks. The relation is
explicitly the disjoint union of the two internal equivalence relations and
equality. -/
def twoBlockBoundary (A B : Set V) (hAB : Disjoint A B) : BoundaryCondition V where
  boundary := A ∪ B
  partition := (BoundaryCondition.wired A).partition ⊔
    (BoundaryCondition.wired B).partition
  supported := by
    intro x y h
    have heq : (twoBlockSetoid A B hAB).r x y := by
      rw [twoBlockSetoid_eq_sup A B hAB]
      exact h
    rcases heq with heq | hA | hB
    · exact Or.inl heq
    · exact Or.inr ⟨Or.inl hA.1, Or.inl hA.2⟩
    · exact Or.inr ⟨Or.inr hB.1, Or.inr hB.2⟩

omit [Finite V] in
theorem twoBlockBoundary_partition_rel (A B : Set V) (hAB : Disjoint A B)
    (x y : V) :
    (twoBlockBoundary A B hAB).partition.r x y ↔
      x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
  change ((BoundaryCondition.wired A).partition ⊔
      (BoundaryCondition.wired B).partition).r x y ↔ _
  rw [← twoBlockSetoid_eq_sup A B hAB]
  rfl

omit [Finite V] in
/-- Merging one vertex from each of two disjoint wired blocks yields the
single wired block on their union. -/
theorem twoBlockBoundary_merge_partition (A B : Set V) (hAB : Disjoint A B)
    {u v : V} (hu : u ∈ A) (hv : v ∈ B) :
    (boundaryMerge (twoBlockBoundary A B hAB) u v).partition =
      (BoundaryCondition.wired (A ∪ B)).partition := by
  classical
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    let S : Setoid V :=
      ((BoundaryCondition.wired A).partition ⊔
        (BoundaryCondition.wired B).partition) ⊔
        (BoundaryCondition.wired ({u, v} : Set V)).partition
    change S.r x y at h
    have hA : (BoundaryCondition.wired A).partition ≤
        (BoundaryCondition.wired (A ∪ B)).partition := by
      intro a b hab
      rw [BoundaryCondition.wired_rel] at hab ⊢
      rcases hab with hab | hab
      · exact Or.inl hab
      · exact Or.inr ⟨Or.inl hab.1, Or.inl hab.2⟩
    have hB : (BoundaryCondition.wired B).partition ≤
        (BoundaryCondition.wired (A ∪ B)).partition := by
      intro a b hab
      rw [BoundaryCondition.wired_rel] at hab ⊢
      rcases hab with hab | hab
      · exact Or.inl hab
      · exact Or.inr ⟨Or.inr hab.1, Or.inr hab.2⟩
    have hUV : (BoundaryCondition.wired ({u, v} : Set V)).partition ≤
        (BoundaryCondition.wired (A ∪ B)).partition := by
      intro a b hab
      rw [BoundaryCondition.wired_rel] at hab ⊢
      rcases hab with hab | hab
      · exact Or.inl hab
      · rcases hab.1 with rfl | rfl <;> rcases hab.2 with rfl | rfl <;>
          simp [hu, hv]
    exact (sup_le (sup_le hA hB) hUV) h
  · intro h
    rw [BoundaryCondition.wired_rel] at h
    let S : Setoid V :=
      ((BoundaryCondition.wired A).partition ⊔
        (BoundaryCondition.wired B).partition) ⊔
        (BoundaryCondition.wired ({u, v} : Set V)).partition
    change S.r x y
    have hA : (BoundaryCondition.wired A).partition ≤ S :=
      le_trans le_sup_left le_sup_left
    have hB : (BoundaryCondition.wired B).partition ≤ S :=
      le_trans le_sup_right le_sup_left
    have hUV : (BoundaryCondition.wired ({u, v} : Set V)).partition ≤ S :=
      le_sup_right
    rcases h with h | h
    · subst y
      exact S.refl x
    · rcases h.1 with hxA | hxB <;> rcases h.2 with hyA | hyB
      · exact hA ((BoundaryCondition.wired_rel A x y).mpr (Or.inr ⟨hxA, hyA⟩))
      · exact Setoid.trans' S
          (hA ((BoundaryCondition.wired_rel A x u).mpr (Or.inr ⟨hxA, hu⟩)))
          (Setoid.trans' S
            (hUV ((BoundaryCondition.wired_rel ({u, v} : Set V) u v).mpr
              (Or.inr ⟨by simp, by simp⟩)))
            (hB ((BoundaryCondition.wired_rel B v y).mpr (Or.inr ⟨hv, hyB⟩))))
      · exact Setoid.trans' S
          (hB ((BoundaryCondition.wired_rel B x v).mpr (Or.inr ⟨hxB, hv⟩)))
          (Setoid.trans' S
            (hUV ((BoundaryCondition.wired_rel ({u, v} : Set V) v u).mpr
              (Or.inr ⟨by simp, by simp⟩)))
            (hA ((BoundaryCondition.wired_rel A u y).mpr (Or.inr ⟨hu, hyA⟩))))
      · exact hB ((BoundaryCondition.wired_rel B x y).mpr (Or.inr ⟨hxB, hyB⟩))

theorem measure_twoBlockBoundary_merge_le_mul (q : Parameters)
    (A B : Set V) (hAB : Disjoint A B) {u v : V}
    (hu : u ∈ A) (hv : v ∈ B) (G : SimpleGraph V)
    (S : Set (Configuration G)) :
    (measure G q (BoundaryCondition.wired (A ∪ B)) S).toReal ≤
      q.val * (measure G q (twoBlockBoundary A B hAB) S).toReal := by
  have hlaw := law_eq_of_boundary_partition_eq (G := G) q _ _
    (twoBlockBoundary_merge_partition A B hAB hu hv)
  have hmeasure : measure G q (boundaryMerge (twoBlockBoundary A B hAB) u v) S =
      measure G q (BoundaryCondition.wired (A ∪ B)) S := by
    unfold PD.FK.measure
    rw [hlaw]
  rw [← hmeasure]
  exact measure_boundaryMerge_le_mul q (twoBlockBoundary A B hAB) u v S

end
end PottsContinuity.BD12
