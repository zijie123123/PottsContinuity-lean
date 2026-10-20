module

public import PottsContinuity.PD.FK.ProbabilityProduct
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Exact finite conditional-law transport under a configuration bijection

The conditioning event is transported together with the full sample law.
Its positive-mass witness is mapped directly, with no event replaced.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- Conditioning and a finite bijection commute with the literal transported
event and its mapped support witness. -/
theorem finite_pmf_filter_map_equiv {α β : Type*} [Finite α] [Finite β]
    (p : PMF α) (e : α ≃ β) (S : Set α) (hS : ∃ a ∈ S, a ∈ p.support) :
    (p.filter S hS).map e =
      (p.map e).filter (e.symm ⁻¹' S) (by
        obtain ⟨a,ha,hpa⟩ := hS
        exact ⟨e a,by simpa only [Set.mem_preimage,Equiv.symm_apply_apply] using ha,
          (PMF.mem_support_map_iff e p (e a)).mpr ⟨a,hpa,rfl⟩⟩) := by
  classical
  let : Fintype α := Fintype.ofFinite _
  let : Fintype β := Fintype.ofFinite _
  have hsum : (∑' a : α, if a ∈ S then p a else 0) =
      ∑' b : β, if e.symm b ∈ S then p (e.symm b) else 0 := by
    rw [tsum_fintype,tsum_fintype]
    exact (e.symm.sum_comp (fun a => if a ∈ S then p a else 0)).symm
  ext b
  rw [FiniteProbability.map_equiv_apply,PMF.filter_apply,PMF.filter_apply]
  simp only [Set.indicator_apply,Set.mem_preimage,FiniteProbability.map_equiv_apply]
  rw [hsum]

end
end PottsContinuity.Thm3.Prop4
