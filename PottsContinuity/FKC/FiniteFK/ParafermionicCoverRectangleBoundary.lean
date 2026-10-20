-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverRectangleBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRectangle
public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import PottsContinuity.FKC.FiniteFK.EmbeddedBoundaryComparison

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

attribute [local instance] configurationMeasurableSpace

abbrev ParafermionicStripVertex (n : ℕ) := RectangleVertex (-(n : ℤ), 0) (2 * n) n
abbrev ParafermionicStripGraph (n : ℕ) := rectangleGraph (-(n : ℤ), 0) (2 * n) n
abbrev ParafermionicAmbientVertex (n : ℕ) := ParafermionicCoverBoxVertex n
abbrev ParafermionicAmbientGraph (n : ℕ) := parafermionicCoverBoxGraph n

def parafermionicCoverStripBottom (n : ℕ) : Set (ParafermionicStripVertex n) :=
  {v | v.1.2 = 0}

def parafermionicCoverStripEmbedding (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    ParafermionicStripVertex n ↪ ParafermionicAmbientVertex n where
  toFun := parafermionicCoverRectangleLift n k hk
  inj' := parafermionicCoverRectangleLift_injective n k hk

def parafermionicCoverStripExteriorOrBottom (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    Set (ParafermionicAmbientVertex n) :=
  (Set.range (parafermionicCoverStripEmbedding n k hk))ᶜ ∪
    (parafermionicCoverStripEmbedding n k hk) '' parafermionicCoverStripBottom n

local instance stripBoundaryInnerEdgeFintype (n : ℕ) :
    Fintype (ParafermionicStripGraph n).edgeSet := Fintype.ofFinite _
local instance stripBoundaryInnerEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicStripGraph n).edgeSet := Classical.decEq _
local instance stripBoundaryMappedEdgeFintype (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    Fintype ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk)).edgeSet :=
  Fintype.ofFinite _
local instance stripBoundaryAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance stripBoundaryAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

lemma parafermionicCoverStrip_map_le (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    (ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk) ≤
      ParafermionicAmbientGraph n := by
  intro x y hxy
  rcases (SimpleGraph.map_adj (parafermionicCoverStripEmbedding n k hk)
      (ParafermionicStripGraph n) x y).mp hxy with ⟨u, v, huv, hux, hvy⟩
  rw [← hux, ← hvy]
  exact (parafermionicCoverRectangleEmbedding n k hk).map_rel_iff'.mpr huv

lemma parafermionicCoverRemovedEdgeEndpoints_mem
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (K : RemovedConfiguration (ParafermionicAmbientGraph n)
      (subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n))) :
    ∀ ⦃e : (ParafermionicAmbientGraph n).edgeSet⦄, e ∈ K.val →
      ∀ ⦃x : ParafermionicAmbientVertex n⦄, x ∈ e.1 →
        x ∈ parafermionicCoverStripExteriorOrBottom n k hk := by
  intro e he x hx
  have heR : e ∈ subgraphRemovedEdges
      ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
      (ParafermionicAmbientGraph n) := K.property he
  have heNotMapped : e.val ∉
      ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk)).edgeSet :=
    (mem_subgraphRemovedEdges _).mp heR
  obtain ⟨ab, hab⟩ := Sym2.mk_surjective e.val
  rcases ab with ⟨a,b⟩
  have heval : e.val = s(a,b) := hab.symm
  have habAdj : (ParafermionicAmbientGraph n).Adj a b := by
    apply (ParafermionicAmbientGraph n).mem_edgeSet.mp
    rw [← heval]
    exact e.property
  have hxAB : x = a ∨ x = b := by
    rw [heval] at hx
    exact (Sym2.mem_iff').mp hx
  have hnotboth : ¬ (a ∈ Set.range (parafermionicCoverStripEmbedding n k hk) ∧
      b ∈ Set.range (parafermionicCoverStripEmbedding n k hk)) := by
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have htarget : (ParafermionicAmbientGraph n).Adj
        ((parafermionicCoverStripEmbedding n k hk) u)
        ((parafermionicCoverStripEmbedding n k hk) v) := by
      simpa [hu, hv] using habAdj
    have hadjStrip : (ParafermionicStripGraph n).Adj u v :=
      (parafermionicCoverRectangleLift_adj_iff n k hk u v).mp htarget
    have hadjMapped : ((ParafermionicStripGraph n).map
        (parafermionicCoverStripEmbedding n k hk)).Adj a b := by
      exact (SimpleGraph.map_adj (parafermionicCoverStripEmbedding n k hk)
        (ParafermionicStripGraph n) a b).2 ⟨u, v, hadjStrip, hu, hv⟩
    have heMapped : e.val ∈
        ((ParafermionicStripGraph n).map
          (parafermionicCoverStripEmbedding n k hk)).edgeSet := by
      rw [heval]
      exact (SimpleGraph.mem_edgeSet _).2 hadjMapped
    exact heNotMapped heMapped
  rcases hxAB with hxa | hxb
  · rw [hxa]
    by_cases ha : a ∈ Set.range (parafermionicCoverStripEmbedding n k hk)
    · have hb : b ∉ Set.range (parafermionicCoverStripEmbedding n k hk) := by
        intro hb
        exact hnotboth ⟨ha, hb⟩
      right
      obtain ⟨u, hu⟩ := Set.mem_range.mp ha
      have hbottom := parafermionicCoverRectangle_neighbor_inside_endpoint_y_zero
        n k hk a b ⟨u, hu.symm⟩ habAdj (by
          intro r hr
          exact hb (Set.mem_range.mpr ⟨r, hr.symm⟩))
      have hbottom' : u ∈ parafermionicCoverStripBottom n := by
        rw [← hu] at hbottom
        change u.1.2 = 0
        simpa [parafermionicCoverStripEmbedding, parafermionicCoverRectangleEmbedding,
          parafermionicCoverRectangleLift] using hbottom
      exact ⟨u, hbottom', hu⟩
    · exact Or.inl ha
  · rw [hxb]
    by_cases hb : b ∈ Set.range (parafermionicCoverStripEmbedding n k hk)
    · have ha : a ∉ Set.range (parafermionicCoverStripEmbedding n k hk) := by
        intro ha
        exact hnotboth ⟨ha, hb⟩
      right
      obtain ⟨u, hu⟩ := Set.mem_range.mp hb
      have hbottom := parafermionicCoverRectangle_neighbor_inside_endpoint_y_zero
        n k hk b a ⟨u, hu.symm⟩ habAdj.symm (by
          intro r hr
          exact ha (Set.mem_range.mpr ⟨r, hr.symm⟩))
      have hbottom' : u ∈ parafermionicCoverStripBottom n := by
        rw [← hu] at hbottom
        change u.1.2 = 0
        simpa [parafermionicCoverStripEmbedding, parafermionicCoverRectangleEmbedding,
          parafermionicCoverRectangleLift] using hbottom
      exact ⟨u, hbottom', hu⟩
    · exact Or.inl hb


lemma parafermionicCoverStripEmbedding_memExteriorOrBottom_iff
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (v : ParafermionicStripVertex n) :
    (parafermionicCoverStripEmbedding n k hk v ∈
      parafermionicCoverStripExteriorOrBottom n k hk) ↔ v.1.2 = 0 := by
  change (parafermionicCoverStripEmbedding n k hk v ∈
      (Set.range (parafermionicCoverStripEmbedding n k hk))ᶜ ∪
        (parafermionicCoverStripEmbedding n k hk) '' parafermionicCoverStripBottom n) ↔ _
  rw [Set.mem_union, Set.mem_compl_iff, Set.mem_range]
  constructor
  · rintro (hnot | ⟨u, huBottom, heq⟩)
    · exact False.elim (hnot ⟨v, rfl⟩)
    · have huv : u = v := (parafermionicCoverStripEmbedding n k hk).injective heq
      simpa [parafermionicCoverStripBottom, huv] using huBottom
  · intro hvBottom
    exact Or.inr ⟨v, hvBottom, rfl⟩

theorem parafermionicCoverStrip_frozenFree_partition_le_bottomWired
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (K : RemovedConfiguration (ParafermionicAmbientGraph n)
      (subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n))) :
    (isolatedExtensionPullbackBoundary (parafermionicCoverStripEmbedding n k hk)
      (frozenBoundary (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        K.val)).partition ≤
      (BoundaryCondition.wired (parafermionicCoverStripBottom n)).partition := by
  let f := parafermionicCoverStripEmbedding n k hk
  let D := parafermionicCoverStripExteriorOrBottom n k hk
  let ξ := BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))
  have hwhole : componentSetoid (ParafermionicAmbientGraph n) ξ K.val ≤
      (BoundaryCondition.wired D).partition := by
    simpa [ξ, D, BoundaryCondition.free, Set.empty_union] using
      componentSetoid_le_wired_union_of_edge_endpoints ξ D K.val
        (parafermionicCoverRemovedEdgeEndpoints_mem n k hk K)
  intro u v huv
  have hcomp : (componentSetoid (ParafermionicAmbientGraph n) ξ K.val).r (f u) (f v) :=
    (Setoid.comap_rel f (componentSetoid (ParafermionicAmbientGraph n) ξ K.val) u v).mp huv
  have hD := hwhole hcomp
  rw [BoundaryCondition.wired_rel] at hD
  rcases hD with heq | ⟨huD, hvD⟩
  · exact (BoundaryCondition.wired_rel _ _ _).mpr (Or.inl (f.injective heq))
  · exact (BoundaryCondition.wired_rel _ _ _).mpr (Or.inr ⟨
      (parafermionicCoverStripEmbedding_memExteriorOrBottom_iff n k hk u).mp huD,
      (parafermionicCoverStripEmbedding_memExteriorOrBottom_iff n k hk v).mp hvD⟩)


theorem measure_parafermionicCoverStrip_frozenFree_le_bottomWired
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (q : ClusterWeight)
    (K : RemovedConfiguration (ParafermionicAmbientGraph n)
      (subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n)) )
    (E : Set (Configuration (ParafermionicStripGraph n))) (hE : IsUpperSet E) :
    (measure (ParafermionicStripGraph n) q
      (isolatedExtensionPullbackBoundary (parafermionicCoverStripEmbedding n k hk)
        (frozenBoundary (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
          K.val)) E).toReal ≤
    (measure (ParafermionicStripGraph n) q
      (BoundaryCondition.wired (parafermionicCoverStripBottom n)) E).toReal := by
  let ξ := isolatedExtensionPullbackBoundary (parafermionicCoverStripEmbedding n k hk)
    (frozenBoundary (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) K.val)
  have hboundary : ξ.partition ≤
      (BoundaryCondition.wired (parafermionicCoverStripBottom n)).partition := by
    simpa [ξ] using parafermionicCoverStrip_frozenFree_partition_le_bottomWired n k hk K
  exact measure_boundary_comparison q ξ (BoundaryCondition.wired
    (parafermionicCoverStripBottom n)) hboundary E hE

theorem filtered_parafermionicCoverStrip_frozenFree_probability_le_bottomWired
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (q : ClusterWeight)
    (K : RemovedConfiguration (ParafermionicAmbientGraph n)
      (subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n)))
    (E : Set (Configuration (ParafermionicStripGraph n))) (hE : IsUpperSet E) :
    ((((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).filter
      (frozenStateEvent
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)
      (frozenStateEvent_support q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)).map
      (embeddedConfigurationRestriction (ParafermionicStripGraph n)
        (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
        (parafermionicCoverStrip_map_le n k hk))).toMeasure E).toReal ≤
    (measure (ParafermionicStripGraph n) q
      (BoundaryCondition.wired (parafermionicCoverStripBottom n)) E).toReal := by
  rw [law_filter_frozen_map_embeddedRestriction
    (ParafermionicStripGraph n) (ParafermionicAmbientGraph n)
    (parafermionicCoverStripEmbedding n k hk)
    (parafermionicCoverStrip_map_le n k hk) q
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) K]
  exact measure_parafermionicCoverStrip_frozenFree_le_bottomWired n k hk q K E hE

end
end PottsContinuity.FKC.FiniteFK
