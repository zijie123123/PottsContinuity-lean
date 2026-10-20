module

public import PottsContinuity.BD12.PositiveMarginal
public import Mathlib.Logic.Equiv.Set

/-! Canonical marginalisation along any finite coordinate partition. The
retained carrier contains only retained edges, and every outside state is
summed with its original weight. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped BigOperators
noncomputable section
variable {E F O : Type*} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] [Fintype O] [DecidableEq O]

/-- Relabel a positive configuration weight by an edge equivalence. -/
def finiteReindexedWeight (e : E ≃ O) (w : Finset O → Set.Ioi (0 : ℝ))
    (A : Finset E) : Set.Ioi (0 : ℝ) := w (A.map e.toEmbedding)

omit [Fintype E] [Fintype O] in
theorem finiteReindexedWeight_lattice_condition (e : E ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (A B : Finset E) :
    (finiteReindexedWeight e w A : ℝ) * finiteReindexedWeight e w B ≤
      (finiteReindexedWeight e w (A ∩ B) : ℝ) * finiteReindexedWeight e w (A ∪ B) := by
  simpa only [finiteReindexedWeight, Finset.map_inter, Finset.map_union] using
    hw (A.map e.toEmbedding) (B.map e.toEmbedding)

theorem finiteReindexedWeight_mean (e : E ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) :
    finitePinnedMean (finiteReindexedWeight e w) ∅ ∅ f =
      finitePinnedMean w ∅ ∅ (fun C => f ((Equiv.finsetCongr e).symm C)) := by
  simp only [finitePinnedMean, finitePinnedWeight, Finset.inter_empty, ite_true,
    finiteReindexedWeight]
  congr 1
  · exact Fintype.sum_equiv (Equiv.finsetCongr e) _ _ (fun A => by
    change (w ((Equiv.finsetCongr e) A) : ℝ) * f A =
      (w ((Equiv.finsetCongr e) A) : ℝ) * f ((Equiv.finsetCongr e).symm ((Equiv.finsetCongr e) A))
    rw [Equiv.symm_apply_apply])
  · exact Fintype.sum_equiv (Equiv.finsetCongr e) _ _ (fun A => rfl)

/-- Inner-coordinate marginal of a weight on an arbitrarily labelled outer cube. -/
def finitePartitionMarginalWeight (e : E ⊕ F ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ)) : Finset E → Set.Ioi (0 : ℝ) :=
  finiteLeftMarginalWeight (finiteReindexedWeight e w)

/-- Projection to the retained coordinates of an edge partition. -/
def finitePartitionProjection (e : E ⊕ F ≃ O) (C : Finset O) : Finset E :=
  ((Equiv.finsetCongr e).symm C).toLeft

omit [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype O] [DecidableEq O] in
theorem finitePartitionProjection_monotone (e : E ⊕ F ≃ O) :
    Monotone (finitePartitionProjection e) := by
  intro A B hAB
  exact Finset.toLeft_monotone (Finset.map_subset_map.mpr hAB)

omit [Fintype E] [Fintype O] in
theorem finitePartitionMarginalWeight_lattice_condition (e : E ⊕ F ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (A B : Finset E) :
    (finitePartitionMarginalWeight e w A : ℝ) * finitePartitionMarginalWeight e w B ≤
      (finitePartitionMarginalWeight e w (A ∩ B) : ℝ) * finitePartitionMarginalWeight e w (A ∪ B) :=
  finiteLeftMarginalWeight_lattice_condition _ (finiteReindexedWeight_lattice_condition e w hw) A B

theorem finitePartitionMarginalWeight_mean (e : E ⊕ F ≃ O)
    (w : Finset O → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) :
    finitePinnedMean (finitePartitionMarginalWeight e w) ∅ ∅ f =
      finitePinnedMean w ∅ ∅ (fun C => f (finitePartitionProjection e C)) := by
  rw [finitePartitionMarginalWeight, finiteLeftMarginalWeight_mean,
    finiteReindexedWeight_mean]
  rfl

omit [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype O] [DecidableEq O] in
/-- A retained edge is present in the projection exactly when its original
outer edge is present. -/
theorem finitePartitionProjection_mem (e : E ⊕ F ≃ O) (C : Finset O) (a : E) :
    a ∈ finitePartitionProjection e C ↔ e (Sum.inl a) ∈ C := by
  unfold finitePartitionProjection
  rw [Finset.mem_toLeft]
  change Sum.inl a ∈ C.map e.symm.toEmbedding ↔ e (Sum.inl a) ∈ C
  simp

end
end PottsContinuity.BD12
