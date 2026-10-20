module

public import PottsContinuity.Thm3.Push.ClosedClusterFrontier
public import PottsContinuity.PD.FK.EdgeRestriction
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
variable {G : SimpleGraph V} {H : SimpleGraph W}
local instance labelCutPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance labelCutEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance labelCutEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance labelCutAuxDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- Original bonds crossing the cut of a vertex label on the auxiliary graph.
The definition reads both actual auxiliary endpoints and is independent of
representatives of an unordered edge. -/
def auxiliaryLabelCut (e : G.edgeSet ≃ H.edgeSet) (σ : W → Bool) : Configuration G := by
  classical
  exact Finset.univ.filter fun f =>
    ∃ u ∈ (e f).val, ∃ v ∈ (e f).val, σ u ≠ σ v

omit [Finite W] in
theorem mem_auxiliaryLabelCut_iff (e : G.edgeSet ≃ H.edgeSet) (σ : W → Bool)
    (f : G.edgeSet) (u v : W) (hf : (e f).val = s(u,v)) :
    f ∈ auxiliaryLabelCut e σ ↔ σ u ≠ σ v := by
  classical
  simp [auxiliaryLabelCut, hf, Sym2.mem_iff, ne_comm]

omit [Finite W] in
/-- Every open step in the complement of the label cut preserves the label. -/
theorem auxiliaryClosed_labelCut_adj_preserves (e : G.edgeSet ≃ H.edgeSet) (σ : W → Bool)
    {u v : W} (huv : (openGraph H
      (auxiliaryClosedConfiguration e (auxiliaryLabelCut e σ))).Adj u v) :
    σ u = σ v := by
  classical
  have hb := openGraph_le H _ huv
  let f : H.edgeSet := ⟨s(u,v), H.mem_edgeSet.mpr hb⟩
  have hf : f ∈ auxiliaryClosedConfiguration e (auxiliaryLabelCut e σ) := by
    apply (coe_mem_openEdges_iff H _ f).mp
    exact (openGraph_adj H _ u v).mp huv
  have hnot := (mem_auxiliaryClosedConfiguration e _ f).mp hf
  have heq : (e (e.symm f)).val = s(u,v) := by simp [f]
  exact not_ne_iff.mp (fun h => hnot ((mem_auxiliaryLabelCut_iff e σ _ u v heq).mpr h))

omit [Finite W] in
/-- A whole auxiliary-complement path stays at the same label. -/
theorem auxiliaryClosed_labelCut_reachable_preserves (e : G.edgeSet ≃ H.edgeSet)
    (σ : W → Bool) {u v : W}
    (huv : ActualConnected H (auxiliaryClosedConfiguration e (auxiliaryLabelCut e σ)) u v) :
    σ u = σ v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => rfl
  | cons h p ih => exact (auxiliaryClosed_labelCut_adj_preserves e σ h).trans ih

/-- The cut around the actually explored closed clusters consists of original
OPEN bonds, and every one of those states is revealed by the exploration. -/
theorem reached_labelCut_subset_open_and_revealed
    (e : G.edgeSet ≃ H.edgeSet) (S : Finset W) (A : Configuration G) :
    auxiliaryLabelCut e (fun v => decide (v ∈ closedClusterReached e S A)) ⊆
      A ∩ closedClusterReveal e S A := by
  classical
  intro f hf
  obtain ⟨u, hu, v, hv, hne⟩ : ∃ u ∈ (e f).val, ∃ v ∈ (e f).val,
      decide (u ∈ closedClusterReached e S A) ≠ decide (v ∈ closedClusterReached e S A) := by
    simpa only [auxiliaryLabelCut, Finset.mem_filter, Finset.mem_univ, true_and] using hf
  have huv : u ≠ v := by intro heq; subst v; exact hne rfl
  have hp : (e f).val = s(u,v) := by
    exact (Sym2.mem_and_mem_iff huv).mp ⟨hu,hv⟩
  have hadj : H.Adj u v := H.mem_edgeSet.mp (hp ▸ (e f).property)
  have hstate : f ∈ A := by
    by_cases hur : u ∈ closedClusterReached e S A
    · have hvr : v ∉ closedClusterReached e S A := by
        intro hvr
        exact hne (by simp only [hur, hvr, decide_true])
      have ht := closedCluster_frontier_primal_open e S A hadj hur hvr
      have he : e.symm ⟨s(u,v), H.mem_edgeSet.mpr hadj⟩ = f := by
        apply e.injective
        simp only [e.apply_symm_apply]
        exact Subtype.ext hp.symm
      simpa only [he] using ht
    · have hvr : v ∈ closedClusterReached e S A := by
        by_contra hvr
        exact hne (by simp only [hur, hvr, decide_false])
      have ht := closedCluster_frontier_primal_open e S A hadj.symm hvr hur
      have he : e.symm ⟨s(v,u), H.mem_edgeSet.mpr hadj.symm⟩ = f := by
        apply e.injective
        simp only [e.apply_symm_apply]
        exact Subtype.ext (Sym2.eq_swap.trans hp.symm)
      simpa only [he] using ht
  refine Finset.mem_inter.mpr ⟨hstate, ?_⟩
  apply (mem_closedClusterReveal_iff_endpoint e S A f).mpr
  by_cases hur : u ∈ closedClusterReached e S A
  · exact ⟨u, hu, hur⟩
  · have hvr : v ∈ closedClusterReached e S A := by
      by_contra hvr
      exact hne (by simp only [hur, hvr, decide_false])
    exact ⟨v, hv, hvr⟩

end
end PottsContinuity.Push
