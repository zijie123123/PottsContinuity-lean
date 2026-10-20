module

public import PottsContinuity.PD.Duality.FiniteDuality
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
open scoped BigOperators
noncomputable section

/-- Exact conditioning commutes with a bijective finite change of actual
sample carrier. The target event is the literal inverse-image event. -/
theorem pmf_filter_map_equiv {α β : Type*} [Finite α] [Finite β]
    (p : PMF α) (e : α ≃ β) (E : Set α) (h : ∃ a ∈ E, a ∈ p.support) :
    (p.filter E h).map e = (p.map e).filter (e.symm ⁻¹' E) (by
      obtain ⟨a,ha,hp⟩ := h
      refine ⟨e a,by simpa using ha,?_⟩
      change p.map e (e a) ≠ 0
      rw [FiniteProbability.map_equiv_apply,e.symm_apply_apply]
      exact hp) := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let : Fintype β := Fintype.ofFinite _
  have hm : (∑' a, E.indicator p a) =
      ∑' b, (e.symm ⁻¹' E).indicator (p.map e) b := by
    rw [tsum_fintype,tsum_fintype,← e.sum_comp]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Set.indicator_apply,Set.mem_preimage,FiniteProbability.map_equiv_apply,
      e.symm_apply_apply]
  ext b
  rw [FiniteProbability.map_equiv_apply,PMF.filter_apply,PMF.filter_apply,hm]
  simp only [Set.indicator_apply,Set.mem_preimage,FiniteProbability.map_equiv_apply]

end
end PottsContinuity.RSW
