module

public import PottsContinuity.BD12.MarginalCovariance
public import Mathlib.Tactic

/-! Coordinate partition induced by an injection. Its range equivalence has
unique preimages; no configuration or boundary condition is selected. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {E O : Type*}

/-- Every embedded coordinate is retained, and all other coordinates form the
literal complement of its range. -/
def finiteEmbeddingPartition (i : E ↪ O) :
    E ⊕ {a : O // a ∉ Set.range i} ≃ O := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective i i.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range i))

variable [Fintype E] [Fintype O] [DecidableEq E] [DecidableEq O]

omit [DecidableEq E] [Fintype E] [Fintype O] [DecidableEq O] in
/-- The edge restriction is the inverse image of the outer configuration. -/
theorem finiteEmbeddingPartition_projection_mem (i : E ↪ O) (C : Finset O) (a : E) :
    a ∈ finitePartitionProjection (finiteEmbeddingPartition i) C ↔ i a ∈ C :=
  finitePartitionProjection_mem (finiteEmbeddingPartition i) C a

end
end PottsContinuity.BD12
