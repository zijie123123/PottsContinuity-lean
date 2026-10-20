module

public import PottsContinuity.Thm4.EndpointPassage
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4
noncomputable section

/-- A witness from a fixed finite set survives endpoint passage. Witnesses may
vary with q; no common witness or arbitrary nonunique choice is assumed. -/
theorem continuous_finite_witness_at_four {U : Type*} (S : Finset U)
    (f : Set.Ici (1 : ℝ) → ℝ) (g : U → Set.Ici (1 : ℝ) → ℝ)
    (hf : Continuous f) (hg : ∀ u ∈ S, Continuous (g u))
    (h : ∀ q : Set.Ici (1 : ℝ), q.val < 4 → ∃ u ∈ S, f q ≤ g u q) :
    ∃ u ∈ S, f ⟨4, by norm_num⟩ ≤ g u ⟨4, by norm_num⟩ := by
  classical
  have hS : S.Nonempty := by
    obtain ⟨u, hu, _⟩ := h ⟨1, by norm_num⟩ (by norm_num)
    exact ⟨u, hu⟩
  have hsup := Continuous.finset_sup'_apply hS hg
  have hfour := continuous_le_at_four f (fun q => S.sup' hS (fun u => g u q)) hf hsup
    (fun q hq => by
      obtain ⟨u, hu, hbound⟩ := h q hq
      exact hbound.trans (Finset.le_sup' (fun u => g u q) hu))
  obtain ⟨u, hu, hmax⟩ := Finset.exists_mem_eq_sup' hS (fun u => g u ⟨4, by norm_num⟩)
  exact ⟨u, hu, hfour.trans_eq hmax⟩

end
end PottsContinuity.Thm4
