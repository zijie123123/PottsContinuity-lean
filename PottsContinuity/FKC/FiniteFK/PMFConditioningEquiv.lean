-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/PMFConditioningEquiv.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

open ENNReal

/-- A nonempty filtering event remains nonempty after transporting the PMF and
its event through an equivalence. -/
theorem pmf_map_equiv_filter_witness {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (e : α ≃ β) (S : Set α)
    (h : ∃ a ∈ S, a ∈ p.support) :
    ∃ b ∈ e '' S, b ∈ (p.map e).support := by
  rcases h with ⟨a,ha,hp⟩
  refine ⟨e a, ⟨a,ha,rfl⟩, ?_⟩
  rw [PMF.support_map]
  exact Set.mem_image_of_mem e hp

/-- Filtering a PMF and then transporting by an equivalence is the same
normalized conditional PMF as transporting first and filtering the image event.
Both normalizers are reindexed from the same finite fibers. -/
theorem pmf_filter_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (e : α ≃ β) (S : Set α)
    (h : ∃ a ∈ S, a ∈ p.support) :
    (p.filter S h).map e =
      (p.map e).filter (e '' S) (pmf_map_equiv_filter_witness p e S h) := by
  classical
  have hmass : (∑' a, S.indicator p a) =
      (∑' b, (e '' S).indicator (p.map e) b) := by
    rw [tsum_fintype, tsum_fintype, ← e.sum_comp]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Set.indicator_apply, Set.mem_image]
    simp [PMF.map_apply, tsum_fintype, e.injective.eq_iff]
  have hmap (b : β) : (p.map e) b = p (e.symm b) := by
    rw [PMF.map_apply, tsum_fintype, ← e.symm.sum_comp]
    simp
  ext b
  rw [PMF.map_apply, tsum_fintype, ← e.symm.sum_comp]
  simp only [PMF.filter_apply]
  rw [hmass]
  simp [Set.indicator_apply, hmap]

end
end PottsContinuity.FKC.FiniteFK
