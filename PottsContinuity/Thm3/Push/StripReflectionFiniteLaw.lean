module

public import PottsContinuity.Thm3.Push.StripHorizontalReflection
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Reflection preserves the actual finite top-and-optional-side boundary
partition, including its corner identifications. -/
theorem stripWindow_reflection_boundary_partition (n m : ℕ) (i : Fin 2) :
    (boundaryConditionIso (stripWindowHorizontalReflectionIso n m)
      (RSW.stripWindowBoundary n m i)).partition =
        (RSW.stripWindowBoundary n m i).partition := by
  apply Setoid.ext
  intro u v
  change (_ = _ ∨ _ ∧ _) ↔ (u = v ∨ _ ∧ _)
  have heq : (stripWindowHorizontalReflectionIso n m).symm u =
      (stripWindowHorizontalReflectionIso n m).symm v ↔ u = v :=
    (stripWindowHorizontalReflectionIso n m).symm.injective.eq_iff
  rw [heq]
  have hmem (w : (RSW.stripWindow n m : Set (ℤ × ℤ))) :
      (stripWindowHorizontalReflectionIso n m).symm w ∈ RSW.stripWindowWiredVertices n m i ↔
        w ∈ RSW.stripWindowWiredVertices n m i := by
    change (w.val.2=3*(n:ℤ) ∨ i=1 ∧ (-w.val.1= -(m:ℤ) ∨ -w.val.1=m)) ↔
      (w.val.2=3*(n:ℤ) ∨ i=1 ∧ (w.val.1= -(m:ℤ) ∨ w.val.1=m))
    omega
  rw [hmem u,hmem v]

/-- The finite FK law with the actual strip boundary is invariant under
reflection, for all interior edge parameters and real cluster weights at least one. -/
theorem stripWindow_law_reflection_map (θ : Parameters) (n m : ℕ) (i : Fin 2) :
    (law (squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ))) θ
      (RSW.stripWindowBoundary n m i)).map
        (configurationIso (stripWindowHorizontalReflectionIso n m)) =
    law (squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ))) θ
      (RSW.stripWindowBoundary n m i) := by
  exact (law_configurationIso_map θ (stripWindowHorizontalReflectionIso n m)
    (RSW.stripWindowBoundary n m i)).trans
      (law_eq_of_boundary_partition_eq θ _ _ (stripWindow_reflection_boundary_partition n m i))

end
end PottsContinuity.Push
