module

public import PottsContinuity.Thm3.Push.ConfinedPrefixSelector
public import PottsContinuity.Thm3.Push.IntervalArmFilledRecord
public import PottsContinuity.DualityExt.CrossingRestriction
public import PottsContinuity.PlanarMixed.RetainedWalk

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK Push BD12 Exploration
noncomputable section

abbrev PrefixSourceVertex (n : ℕ) := RectangleVertex (0,0) (2*n) (2*n)
abbrev PrefixAuxVertex (n : ℕ) := RectangleVertex (0,0) (2*n+1) (2*n+1)
abbrev prefixAuxGraph (n : ℕ) := rectangleGraph (0,0) (2*n+1) (2*n+1)

theorem prefix_padding_rectangle_subset (n : ℕ) :
    PD.FK.latticeRectangle (0,0) (2*n) (2*n) ⊆
      PD.FK.latticeRectangle (0,0) (2*n+1) (2*n+1) := by
  intro v hv
  rw [PD.FK.mem_latticeRectangle] at hv ⊢
  norm_num only [Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_one] at hv ⊢
  omega

def prefixPaddingEmbedding (n : ℕ) : PrefixSourceVertex n ↪ PrefixAuxVertex n :=
  DualityExt.rectangleVertexEmbedding (prefix_padding_rectangle_subset n)

theorem confinedPrefix_padding_map_le (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) :
    (caseTwoConfinedPrefixGraph n s hfit b).map (prefixPaddingEmbedding n) ≤ prefixAuxGraph n := by
  intro u v h
  obtain ⟨a,c,hac,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
  have hbase := caseTwoConfinedPrefixGraph_map_le n s hfit b
  change (caseTwoConfinedPrefixGraph n s hfit b).map id ≤ _ at hbase
  rw [SimpleGraph.map_id] at hbase
  exact (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (prefix_padding_rectangle_subset n))
    ((SimpleGraph.map_adj _ _ _ _).mpr ⟨a,c,hbase hac,rfl,rfl⟩)

/-- The padded stopping ray, including its single added top vertex. -/
def prefixAuxRay (n s : ℕ) (b : CaseTwoTipEndpointRecord n s) : Set (PrefixAuxVertex n) :=
  {u | u.val.1=4*(s:ℤ)-1 ∧ b.2.val.2 ≤ u.val.2}

/-- Fixed auxiliary ray bonds carry no queried source state. -/
def prefixAuxRayBonds (n s : ℕ) (b : CaseTwoTipEndpointRecord n s) :
    Configuration (prefixAuxGraph n) := by
  classical
  exact Finset.univ.filter fun e => ∀ u ∈ e.val, u ∈ prefixAuxRay n s b

/-- Only actual confined source states and the fixed ray are opened.
All other padded bonds stay closed. -/
def prefixAuxCompletion (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) : Configuration (prefixAuxGraph n) :=
  embeddedConfigurationEmbedding _ _ (prefixPaddingEmbedding n) (confinedPrefix_padding_map_le n s hfit b)
    (caseTwoConfinedPrefixConfiguration n s hfit b C) ∪ prefixAuxRayBonds n s b

theorem prefixAuxCompletion_open_edge_cases (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (e : (prefixAuxGraph n).edgeSet) (he : e ∈ prefixAuxCompletion n s hfit b C) :
    (∃ f ∈ caseTwoConfinedPrefixConfiguration n s hfit b C,
      embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n) (confinedPrefix_padding_map_le n s hfit b) f=e) ∨
      ∀ u ∈ e.val, u ∈ prefixAuxRay n s b := by
  classical
  rcases Finset.mem_union.mp he with he | he
  · left
    rw [embeddedConfigurationEmbedding_eq_map] at he
    exact Finset.mem_map.mp he
  · right
    simpa only [prefixAuxRayBonds,Finset.mem_filter,Finset.mem_univ,true_and] using he

/-- Every padded top vertex incident to an open bond lies on the fixed ray. -/
theorem prefixAuxCompletion_top_open_vertex_on_ray (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (u v : PrefixAuxVertex n)
    (hu : u.val.2=((2*n+1:ℕ):ℤ))
    (huv : (openGraph (prefixAuxGraph n) (prefixAuxCompletion n s hfit b C)).Adj u v) :
    u ∈ prefixAuxRay n s b := by
  obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ u v).mp huv
  rcases prefixAuxCompletion_open_edge_cases n s hfit b C e he with ⟨f,hf,hfe⟩ | hray
  · have hum : u ∈ Sym2.map (prefixPaddingEmbedding n) f.val := by
      rw [← hfe,embeddedEdgeEmbedding_coe] at heq
      change Sym2.map (prefixPaddingEmbedding n) f.val=s(u,v) at heq
      rw [heq]
      exact Sym2.mem_mk_left _ _
    obtain ⟨z,hz,hzu⟩ := Sym2.mem_map.mp hum
    have hzy := congrArg (fun x : PrefixAuxVertex n => x.val.2) hzu
    have hbound := ((PD.FK.mem_latticeRectangle _ _ _ _).mp z.property).2.2
    change z.val.2=u.val.2 at hzy
    dsimp at hbound
    omega
  · exact hray u (by rw [heq]; exact Sym2.mem_mk_left _ _)

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
