module

public import PottsContinuity.Thm3.Push.ActiveFrontierCarrier
public import PottsContinuity.Thm3.Push.NestedFrontierRestoration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance retentionEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Domination of the actual active-bond restrictions retains every original
unexamined open bond. No statement about virtual boundary connectivity enters
this conversion from configuration order back to original bond states. -/
theorem active_restriction_subset_retains_unexamined {V : Type*} [Finite V]
    (G : SimpleGraph V) (R A B : Configuration G)
    (hsub : embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
        (activeUnexaminedGraph_map_le G R) A ⊆
      embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
        (activeUnexaminedGraph_map_le G R) B) :
    A \ R ⊆ B := by
  classical
  intro f hf
  obtain ⟨hfA,hfR⟩ := Finset.mem_sdiff.mp hf
  let u := f.val.out.1
  let v := f.val.out.2
  have hp : s(u,v)=f.val := Quot.out_eq _
  have huv : G.Adj u v := G.mem_edgeSet.mp (hp.symm ▸ f.property)
  have hdel : (edgeRestriction G R).Adj u v := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨huv,?_⟩
    rw [hp]
    exact fun hmem => hfR ((coe_mem_openEdges_iff G R f).mp hmem)
  have hact := edgeRestriction_adj_active G R hdel
  let x : unexaminedVertices G R := ⟨u,hact.1⟩
  let y : unexaminedVertices G R := ⟨v,hact.2⟩
  let e : (activeUnexaminedGraph G R).edgeSet :=
    ⟨s(x,y),(activeUnexaminedGraph G R).mem_edgeSet.mpr hdel⟩
  have he : embeddedEdgeEmbedding _ _ (Function.Embedding.subtype _)
      (activeUnexaminedGraph_map_le G R) e = f := by
    apply Subtype.ext
    erw [embeddedEdgeEmbedding_coe]
    exact hp
  have heA : e ∈ embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
      (activeUnexaminedGraph_map_le G R) A := by
    rw [mem_embeddedConfigurationRestriction,he]
    exact hfA
  have heB := hsub heA
  rw [mem_embeddedConfigurationRestriction,he] at heB
  exact heB

/-- Concrete shorter-target restoration on a filled-exploration fiber, with
its retention condition discharged by order on actual active configurations. -/
theorem nested_crossing_of_active_restriction_domination
    (a : LatticeVertex) (w h H : ℕ) (hle : h ≤ H)
    (A₀ A B : Configuration (rectangleGraph a w H))
    (h₀ : A₀ ∈ rectangleHorizontalCrossingEvent a w H)
    (hrecord : A ∩ rectangleFilledTopReveal a w H A₀ =
      A₀ ∩ rectangleFilledTopReveal a w H A₀)
    (hsub : embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
        (activeUnexaminedGraph_map_le _ (rectangleFilledTopReveal a w H A₀)) B ⊆
      embeddedConfigurationRestriction _ _ (Function.Embedding.subtype _)
        (activeUnexaminedGraph_map_le _ (rectangleFilledTopReveal a w H A₀)) A)
    (hB : DualityExt.rectangleConfigurationRestriction
      (rectangle_height_subset a w h H hle) B ∈ rectangleHorizontalCrossingEvent a w h) :
    DualityExt.rectangleConfigurationRestriction
      (rectangle_height_subset a w h H hle) A ∈ rectangleHorizontalCrossingEvent a w h := by
  exact nested_crossing_on_filled_record a w h H hle A₀ A B h₀ hrecord
    (active_restriction_subset_retains_unexamined _ _ _ _ hsub) hB

end
end PottsContinuity.Push
