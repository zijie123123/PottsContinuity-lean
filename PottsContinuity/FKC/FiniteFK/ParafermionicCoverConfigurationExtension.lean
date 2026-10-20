-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverConfigurationExtension.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalSheets
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
noncomputable section

local instance coverExtensionEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance coverExtensionEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

def parafermionicCoverBoxVertexEmbedding (n : ℕ) :
    ParafermionicAmbientVertex n ↪ ParafermionicCoverVertex :=
  Function.Embedding.subtype _

theorem parafermionicCoverBoxGraph_map_le (n : ℕ) :
    (ParafermionicAmbientGraph n).map (parafermionicCoverBoxVertexEmbedding n) ≤
      parafermionicCoverGraph := by
  intro u v huv
  rcases (SimpleGraph.map_adj (parafermionicCoverBoxVertexEmbedding n)
      (ParafermionicAmbientGraph n) u v).mp huv with ⟨u', v', hadj, hu, hv⟩
  rw [← hu, ← hv]
  simpa [ParafermionicAmbientGraph, parafermionicCoverBoxGraph,
    parafermionicCoverBoxVertexEmbedding] using hadj

/-- Extend a finite-box open-edge configuration by declaring every other
whole-cover edge closed. -/
def parafermionicCoverConfigurationExtension (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    Configuration parafermionicCoverGraph :=
  A.map (embeddedEdgeEmbedding (ParafermionicAmbientGraph n) parafermionicCoverGraph
    (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n))

def parafermionicCoverConfigurationExtensionState (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : parafermionicCoverGraph.edgeSet) : Bool :=
  decide (e ∈ parafermionicCoverConfigurationExtension n A)

@[simp] theorem parafermionicCoverConfigurationExtensionState_eq_true_iff
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : parafermionicCoverGraph.edgeSet) :
    parafermionicCoverConfigurationExtensionState n A e = true ↔
      e ∈ parafermionicCoverConfigurationExtension n A := by
  simp [parafermionicCoverConfigurationExtensionState]

theorem parafermionicCoverConfigurationExtension_inside
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    embeddedEdgeEmbedding (ParafermionicAmbientGraph n) parafermionicCoverGraph
      (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n) e ∈
        parafermionicCoverConfigurationExtension n A ↔ e ∈ A := by
  classical
  rw [parafermionicCoverConfigurationExtension, Finset.mem_map]
  constructor
  · rintro ⟨e', he', heq⟩
    have : e' = e := (embeddedEdgeEmbedding
      (ParafermionicAmbientGraph n) parafermionicCoverGraph
      (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n)).injective heq
    simpa [this] using he'
  · intro he
    exact ⟨e, he, rfl⟩

theorem parafermionicCoverConfigurationExtensionState_true_endpoints_in_box
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : parafermionicCoverGraph.edgeSet)
    (hstate : parafermionicCoverConfigurationExtensionState n A e = true) :
    ∀ v ∈ e.1, v ∈ parafermionicCoverBoxVertices n := by
  classical
  have hm := (parafermionicCoverConfigurationExtensionState_eq_true_iff n A e).mp hstate
  obtain ⟨e₀, _, he₀⟩ := Finset.mem_map.mp hm
  obtain ⟨ab, hab⟩ := Sym2.mk_surjective e₀.1
  rcases ab with ⟨a, b⟩
  have heval : e.1 = Sym2.map (parafermionicCoverBoxVertexEmbedding n) e₀.1 := by
    exact (congrArg Subtype.val he₀).symm
  have hval : e.1 = Sym2.mk (parafermionicCoverBoxVertexEmbedding n a)
      (parafermionicCoverBoxVertexEmbedding n b) := by
    rw [heval, ← hab]
    simp
  intro v hv
  rw [hval] at hv
  rcases (Sym2.mem_iff').mp hv with hv | hv
  · rw [hv]
    exact a.2
  · rw [hv]
    exact b.2

end
end PottsContinuity.FKC.FiniteFK
