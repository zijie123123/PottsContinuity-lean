module

public import PottsContinuity.BD12.TwoBlockBoundaryMerge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Boundary merge costs with an arbitrary pre-existing boundary partition

DCST, proof of eq. (5), TeX lines 1309-1320; BD12 Lemma self-duality.
One elementary merge costs at most q, so two cost at most q². This module
proves only the finite boundary comparison, without a planar dual-law claim.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed

open PD.FK BD12

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

omit [Finite V] in
/-- If each of two sets is already internally wired, joining their union is
exactly one representative merge, even in the presence of other wiring. -/
theorem merge_partition_eq_sup_wired_union (ξ : BoundaryCondition V)
    (A B : Set V)
    (hA : (BoundaryCondition.wired A).partition ≤ ξ.partition)
    (hB : (BoundaryCondition.wired B).partition ≤ ξ.partition)
    {u v : V} (hu : u ∈ A) (hv : v ∈ B) :
    (boundaryMerge ξ u v).partition =
      ξ.partition ⊔ (BoundaryCondition.wired (A ∪ B)).partition := by
  change ξ.partition ⊔ (BoundaryCondition.wired ({u, v} : Set V)).partition = _
  apply le_antisymm
  · apply sup_le le_sup_left
    intro x y hxy
    apply (le_sup_right : (BoundaryCondition.wired (A ∪ B)).partition ≤ _)
    rcases (BoundaryCondition.wired_rel _ x y).mp hxy with hxy | ⟨hx, hy⟩
    · exact (BoundaryCondition.wired_rel _ x y).mpr (Or.inl hxy)
    · have hsub : ({u, v} : Set V) ⊆ A ∪ B := by
        rintro z (rfl | rfl)
        · exact Or.inl hu
        · exact Or.inr hv
      exact (BoundaryCondition.wired_rel _ x y).mpr (Or.inr ⟨hsub hx, hsub hy⟩)
  · apply sup_le le_sup_left
    intro x y hxy
    let S := ξ.partition ⊔ (BoundaryCondition.wired ({u, v} : Set V)).partition
    change S.r x y
    have hA' : (BoundaryCondition.wired A).partition ≤ S := hA.trans le_sup_left
    have hB' : (BoundaryCondition.wired B).partition ≤ S := hB.trans le_sup_left
    have huv : S.r u v := (le_sup_right :
        (BoundaryCondition.wired ({u, v} : Set V)).partition ≤ S)
      ((BoundaryCondition.wired_rel _ u v).mpr (Or.inr ⟨by simp, by simp⟩))
    rcases (BoundaryCondition.wired_rel _ x y).mp hxy with rfl | ⟨hx, hy⟩
    · exact S.refl x
    · rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hA' ((BoundaryCondition.wired_rel _ x y).mpr (Or.inr ⟨hx, hy⟩))
      · exact S.trans
          (hA' ((BoundaryCondition.wired_rel _ x u).mpr (Or.inr ⟨hx, hu⟩)))
          (S.trans huv
            (hB' ((BoundaryCondition.wired_rel _ v y).mpr (Or.inr ⟨hv, hy⟩))))
      · exact S.trans
          (hB' ((BoundaryCondition.wired_rel _ x v).mpr (Or.inr ⟨hx, hv⟩)))
          (S.trans (S.symm huv)
            (hA' ((BoundaryCondition.wired_rel _ u y).mpr (Or.inr ⟨hu, hy⟩))))
      · exact hB' ((BoundaryCondition.wired_rel _ x y).mpr (Or.inr ⟨hx, hy⟩))

/-- Merging two internally wired sets costs at most q for every event.
The resulting boundary is specified by its exact partition, not its label. -/
theorem measure_join_wired_sets_le_mul (q : Parameters)
    (ξ η : BoundaryCondition V) (A B : Set V)
    (hA : (BoundaryCondition.wired A).partition ≤ ξ.partition)
    (hB : (BoundaryCondition.wired B).partition ≤ ξ.partition)
    (hη : η.partition = ξ.partition ⊔ (BoundaryCondition.wired (A ∪ B)).partition)
    (S : Set (Configuration G)) :
    (measure G q η S).toReal ≤ q.val * (measure G q ξ S).toReal := by
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      have hp : (boundaryMerge ξ u v).partition = η.partition :=
        (merge_partition_eq_sup_wired_union ξ A B hA hB hu hv).trans hη.symm
      have hlaw := law_eq_of_boundary_partition_eq (G := G) q _ _ hp
      have hm : measure G q (boundaryMerge ξ u v) S = measure G q η S := by
        unfold PD.FK.measure
        rw [hlaw]
      rw [← hm]
      exact measure_boundaryMerge_le_mul q ξ u v S
    · have hBe : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hb
      have hp : η.partition = ξ.partition := by
        rw [hη, hBe, Set.union_empty, sup_eq_left.mpr hA]
      have hlaw := law_eq_of_boundary_partition_eq (G := G) q _ _ hp
      have hm : measure G q η S = measure G q ξ S := by unfold PD.FK.measure; rw [hlaw]
      rw [hm]
      exact le_mul_of_one_le_left ENNReal.toReal_nonneg q.property
  · have hAe : A = ∅ := Set.not_nonempty_iff_eq_empty.mp ha
    have hp : η.partition = ξ.partition := by
      rw [hη, hAe, Set.empty_union, sup_eq_left.mpr hB]
    have hlaw := law_eq_of_boundary_partition_eq (G := G) q _ _ hp
    have hm : measure G q η S = measure G q ξ S := by unfold PD.FK.measure; rw [hlaw]
    rw [hm]
    exact le_mul_of_one_le_left ENNReal.toReal_nonneg q.property

end
end PottsContinuity.PlanarMixed
