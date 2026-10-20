/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/ParafermionicCoverConfigurationExtension.lean`.
Includes origin/neighbor lemmas from ParafermionicCover{ExtremalSheets,OriginInterior}.lean.
Adaptation: prune unused rectangle/layer probability imports; reuse exact cover graph and PD edge embedding.
-/
module

public import PottsContinuity.Thm4.CoverGraph
public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK
noncomputable section

/-- Full finite cover carrier, retaining all isolated vertices. -/
abbrev ParafermionicAmbientVertex (n : ℕ) := ParafermionicCoverBoxVertex n
abbrev ParafermionicAmbientGraph (n : ℕ) := parafermionicCoverBoxGraph n

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

/-- The origin vertex in the actual finite cover box. -/
def parafermionicCoverBoxOrigin (n : ℕ) : ParafermionicAmbientVertex n :=
  ⟨((0,0),0), by
    rw [parafermionicCoverBoxFinset, Finset.mem_product]
    exact ⟨center_mem_latticeBox (0,0) n, by simp⟩⟩

@[simp] theorem parafermionicCoverBoxOrigin_val (n : ℕ) :
    (parafermionicCoverBoxOrigin n).1 = ((0,0),0) := rfl

/-- The actual neighbors of the cover-box origin are the four base neighbors on sheet zero. -/
theorem parafermionicCoverBoxOrigin_neighbor_cases (n : ℕ)
    {w : ParafermionicCoverVertex}
    (hadj : parafermionicCoverGraph.Adj (parafermionicCoverBoxOrigin n).1 w) :
    w = ((0,1),0) ∨ w = ((0,-1),0) ∨ w = ((1,0),0) ∨ w = ((-1,0),0) := by
  have hbase : parafermionicCoverGraph.Adj ((0,0),0) w := by
    simpa using hadj
  rcases (parafermionicCoverGraph_adj_iff_cases ((0,0),0) w).mp hbase with
    h | h | h | h | h | h | h | h
  all_goals rcases w with ⟨⟨x,y⟩,k⟩
  all_goals simp_all <;> omega

/-- For positive box radius, every actual whole-cover neighbor of the origin is retained. -/
theorem parafermionicCoverBoxOrigin_neighbor_mem_box (n : ℕ) (hn : 1 ≤ n)
    {w : ParafermionicCoverVertex}
    (hadj : parafermionicCoverGraph.Adj (parafermionicCoverBoxOrigin n).1 w) :
    w ∈ parafermionicCoverBoxVertices n := by
  rcases parafermionicCoverBoxOrigin_neighbor_cases n hadj with h | h | h | h
  all_goals rw [parafermionicCoverBoxVertices_mem]
  all_goals rw [h]
  all_goals norm_num
  have hnZ : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  all_goals omega

end
end PottsContinuity.Thm4
