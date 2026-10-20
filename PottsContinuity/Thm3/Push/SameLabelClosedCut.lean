module

public import PottsContinuity.Thm3.Push.AuxiliaryLabelCut
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

omit [Finite W] in
/-- Conversely, every actual auxiliary edge whose endpoint labels agree is
CLOSED relative to the original primal label-cut configuration. -/
theorem auxiliaryClosed_labelCut_adj_of_same_label
    (e : G.edgeSet ≃ H.edgeSet) (σ : W → Bool) {u v : W}
    (huv : H.Adj u v) (hlabel : σ u = σ v) :
    (openGraph H (auxiliaryClosedConfiguration e (auxiliaryLabelCut e σ))).Adj u v := by
  classical
  let f : H.edgeSet := ⟨s(u,v),H.mem_edgeSet.mpr huv⟩
  have he : (e (e.symm f)).val=s(u,v) := by simp only [Equiv.apply_symm_apply]; rfl
  have hnot : e.symm f ∉ auxiliaryLabelCut e σ := by
    intro hf
    exact ((mem_auxiliaryLabelCut_iff e σ _ u v he).mp hf) hlabel
  rw [openGraph_adj]
  exact ⟨f,(mem_auxiliaryClosedConfiguration e _ f).mpr hnot,rfl⟩

/-- The induced graph of any constant-label region embeds its original steps
into the genuine complementary sampled configuration of the primal cut. -/
def constantLabelRegionToClosedCut (e : G.edgeSet ≃ H.edgeSet)
    (σ : W → Bool) (S : Set W) (b : Bool) (hS : ∀ v ∈ S, σ v=b) :
    H.induce S →g openGraph H (auxiliaryClosedConfiguration e (auxiliaryLabelCut e σ)) where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    exact auxiliaryClosed_labelCut_adj_of_same_label e σ huv
      ((hS u u.property).trans (hS v v.property).symm)

omit [Finite W] in
/-- A region connection is consequently an actual CLOSED dual connection,
with both original endpoints unchanged. -/
theorem constantLabelRegion_connected_in_closedCut
    (e : G.edgeSet ≃ H.edgeSet) (σ : W → Bool) (S : Set W) (b : Bool)
    (hS : ∀ v ∈ S, σ v=b) (u v : S) (huv : (H.induce S).Reachable u v) :
    ActualConnected H (auxiliaryClosedConfiguration e (auxiliaryLabelCut e σ)) u.val v.val := by
  obtain ⟨p⟩ := huv
  exact (p.map (constantLabelRegionToClosedCut e σ S b hS)).reachable

end
end PottsContinuity.Push
