/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleMixedCoordinateSwap.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleCrossingSymmetry
public import PottsContinuity.PlanarMixed.Square.RectangleTranslation
public import PottsContinuity.BD12.TwoBlockBoundaryMerge
public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarPartitionUpper
public import Mathlib.Tactic
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

 theorem rectangleDoubleCollar_image_blocks_disjoint
    {V W : Type*} (e : V ≃ W) (A B : Set V) (hAB : Disjoint A B) :
    Disjoint (e '' A) (e '' B) := by
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  rcases hzA with ⟨a, ha, hza⟩
  rcases hzB with ⟨b, hb, hzb⟩
  apply (Set.disjoint_left.mp hAB) ha
  have hab : a = b := e.injective (hza.trans hzb.symm)
  simpa [hab] using hb

theorem boundaryConditionIso_twoBlock_image {V W : Type*}
    [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (A B : Set V) (hAB : Disjoint A B) :
    boundaryConditionIso e (twoBlockBoundary A B hAB) =
      twoBlockBoundary (e '' A) (e '' B)
        (rectangleDoubleCollar_image_blocks_disjoint e.toEquiv A B hAB) := by
  rw [BoundaryCondition.mk.injEq]
  constructor
  · ext x
    change x ∈ e '' (A ∪ B) ↔ x ∈ e '' A ∪ e '' B
    constructor
    · rintro ⟨u, hu | hu, hux⟩
      · exact Or.inl ⟨u, hu, hux⟩
      · exact Or.inr ⟨u, hu, hux⟩
    · rintro (⟨u, hu, hux⟩ | ⟨u, hu, hux⟩)
      · exact ⟨u, Or.inl hu, hux⟩
      · exact ⟨u, Or.inr hu, hux⟩
  · apply Setoid.ext
    intro x y
    change (twoBlockBoundary A B hAB).partition.r (e.symm x) (e.symm y) ↔
      (twoBlockBoundary (e '' A) (e '' B)
        (rectangleDoubleCollar_image_blocks_disjoint e.toEquiv A B hAB)).partition.r x y
    rw [twoBlockBoundary_partition_rel, twoBlockBoundary_partition_rel]
    have heq : e.symm x = e.symm y ↔ x = y := by
      constructor
      · intro h; simpa using congrArg e h
      · intro h; exact congrArg e.symm h
    have hA (z : W) : e.symm z ∈ A ↔ z ∈ e '' A := by
      constructor
      · intro hz; exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
      · rintro ⟨u, hu, hzu⟩
        have heq' : e.symm z = u := by
          simpa using (congrArg e.symm hzu).symm
        simpa [heq'] using hu
    have hB (z : W) : e.symm z ∈ B ↔ z ∈ e '' B := by
      constructor
      · intro hz; exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
      · rintro ⟨u, hu, hzu⟩
        have heq' : e.symm z = u := by
          simpa using (congrArg e.symm hzu).symm
        simpa [heq'] using hu
    simp only [heq, hA x, hA y, hB x, hB y]

end
end PottsContinuity.PlanarMixed.Square
