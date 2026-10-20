module

public import PottsContinuity.Thm3.Push.AuxiliaryLabelCut
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
variable {G : SimpleGraph V} {H : SimpleGraph W}
local instance pathTransferEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance pathTransferAuxDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

omit [Finite W] in
/-- Original opening can only close auxiliary complementary bonds. -/
theorem auxiliaryClosedConfiguration_antitone (e : G.edgeSet ≃ H.edgeSet)
    {A B : Configuration G} (hAB : A ⊆ B) :
    auxiliaryClosedConfiguration e B ⊆ auxiliaryClosedConfiguration e A := by
  intro f hf
  rw [mem_auxiliaryClosedConfiguration] at hf ⊢
  exact fun ha => hf (hAB ha)

omit [Finite W] in
/-- A closed-dual path starting below a cut remains below it when all cut
bonds are open. If original bonds outside the cut region are retained, the
same connection survives in the reference complementary configuration.
This is an edge-state/path statement, with no FK or selector assumption. -/
theorem auxiliaryClosed_path_transfer_below_cut
    (e : G.edgeSet ≃ H.edgeSet) (σ : W → Bool) (A B : Configuration G)
    (hcut : auxiliaryLabelCut e σ ⊆ A)
    (hout : ∀ f : G.edgeSet, (∀ z ∈ (e f).val, σ z = false) → f ∈ B → f ∈ A)
    {u v : W} (hu : σ u = false)
    (hconn : ActualConnected H (auxiliaryClosedConfiguration e A) u v) :
    σ v = false ∧ ActualConnected H (auxiliaryClosedConfiguration e B) u v := by
  have hsub := auxiliaryClosedConfiguration_antitone e hcut
  have hstep : ∀ {x y : W}, σ x = false →
      (openGraph H (auxiliaryClosedConfiguration e A)).Adj x y →
      σ y = false ∧ (openGraph H (auxiliaryClosedConfiguration e B)).Adj x y := by
    intro x y hx hxy
    have hlabel := auxiliaryClosed_labelCut_adj_preserves e σ ((openGraph_mono hsub) hxy)
    have hy : σ y = false := hlabel.symm.trans hx
    have hb := openGraph_le H _ hxy
    let f : H.edgeSet := ⟨s(x,y), H.mem_edgeSet.mpr hb⟩
    have hfA : f ∈ auxiliaryClosedConfiguration e A :=
      (coe_mem_openEdges_iff H _ f).mp ((openGraph_adj H _ x y).mp hxy)
    have hnotA := (mem_auxiliaryClosedConfiguration e A f).mp hfA
    have hlabels : ∀ z ∈ (e (e.symm f)).val, σ z = false := by
      intro z hz
      have hz' : z ∈ s(x,y) := by simpa only [Equiv.apply_symm_apply] using hz
      rcases (Sym2.mem_iff').mp hz' with rfl | rfl
      · exact hx
      · exact hy
    have hfB : f ∈ auxiliaryClosedConfiguration e B := by
      apply (mem_auxiliaryClosedConfiguration e B f).mpr
      exact fun hB => hnotA (hout (e.symm f) hlabels hB)
    refine ⟨hy, ?_⟩
    rw [openGraph_adj]
    exact ⟨f, hfB, rfl⟩
  obtain ⟨p⟩ := hconn
  suffices hall : ∀ {x y : W}
      (p : (openGraph H (auxiliaryClosedConfiguration e A)).Walk x y),
      σ x = false → σ y = false ∧
        Nonempty ((openGraph H (auxiliaryClosedConfiguration e B)).Walk x y) from hall p hu
  intro x y p
  induction p with
  | nil => intro hx; exact ⟨hx, ⟨.nil⟩⟩
  | cons h p ih =>
    intro hx
    obtain ⟨hy, hB⟩ := hstep hx h
    obtain ⟨hz, ⟨pB⟩⟩ := ih hy
    exact ⟨hz, ⟨pB.cons hB⟩⟩

end
end PottsContinuity.Push
