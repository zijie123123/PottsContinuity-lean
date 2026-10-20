module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedBarrierOpen
public import PottsContinuity.PlanarMixed.StripRSWSelectors.CrosscutLeftClosure
public import PottsContinuity.PlanarMixed.StripRSWSelectors.RawLeftQueryContainment
public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedQueryLocality
public import PottsContinuity.PlanarTopology.RectangleCurveExclusion

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK PD.FK.Medial PD.Duality Push BD12 Exploration PlanarMixed.FiniteSlit
noncomputable section
local instance actualPrefixQueryEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- On an actual tip record, every original raw left query lies on the left
of any physical confined first-contact prefix. No locality premise is used. -/
theorem actual_confined_prefix_raw_query_endpoint_left
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s) (trace : List (PrefixSourceVertex n))
    (hb : caseTwoTipEndpointSelector n s hfit C=some b)
    (hpath : ConfinedPrefixFirstContact n s hfit C b trace)
    (e : (rectangleGraph (0,0) (2*n) (2*n)).edgeSet)
    (he : embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n)
      (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (prefix_padding_rectangle_subset n)) e ∈
        intervalArmLeftReveal (2*n+1) (4*(s:ℤ)) (prefixAuxCompletion n s hfit b C))
    (u : PrefixSourceVertex n) (hu : u ∈ e.val) :
    u ∈ pocketAugmentedSourceLeftExterior (2*n) (2*n) (4*(s:ℤ)) b.2.val.2
      (sourceCoordinateTrace (2*n) (2*n) (Subtype.val '' {z | z ∈ trace})) := by
  classical
  obtain ⟨O⟩ := confinedPrefixFirstContact_sourcePaths n s hs hfit C b trace hb hpath
  obtain ⟨a,ha,t,htx,hty,p,hp,hfirst⟩ := hpath
  let U := sourceWalkPairUnderlying _ C O.paths
  have hg := O.geometry
  change RetainedRectanglePathGeometry (2*n) (2*n) (4*(s:ℤ)) U at hg
  obtain ⟨hx,hxw,hUa,hUb,hUtx,hUty,hUvx,hUax,hUab,hUcol,hUdis,hUfirst⟩ := hg
  have hUend : U.secondEnd=b.2 := O.second_end
  have hUty' : b.2.val.2 ≤ U.firstEnd.val.2 := by simpa only [hUend] using hUty
  have hUv : U.secondEnd.val=(4*(s:ℤ),b.2.val.2) :=
    Prod.ext hUvx (congrArg (fun z : PrefixSourceVertex n => z.val.2) hUend)
  have hUfirst' : ∀ i < U.first.length,
      ¬ ((U.first.getVert i).val.1=4*(s:ℤ)-1 ∧ b.2.val.2 ≤ (U.first.getVert i).val.2) := by
    simpa only [hUend] using hUfirst
  obtain ⟨hy,D,hDa,hDb,hDt,hDv,hPs,hQs,hPe,hQe⟩ :=
    sourceRectangle_crosscutData_of_leftContactPrefix (2*n) (2*n) (4*(s:ℤ)) b.2.val.2 hx hxw
      U.first U.second hUa hUb hUax hUab ⟨hUtx,hUty'⟩ hUv hUcol hUdis hUfirst'
  let M := 2*((2*n)+(2*n))+2
  let F := paddedRectangleReference (2*n) (2*n) (4*(s:ℤ)) hx hxw
  let P := (D.first.map (toLattice M (4*(s:ℤ)) b.2.val.2)).copy
    (show D.firstStart.val=(D.firstStart.val.1,0) from Prod.ext rfl D.first_bottom)
    (show D.firstEnd.val=(4*(s:ℤ)-1,D.firstEnd.val.2) from Prod.ext D.first_end_column rfl)
  have hPS : P.support=trace.map Subtype.val := by
    calc
      P.support = D.first.support.map Subtype.val :=
        (SimpleGraph.Walk.support_copy _ _ _).trans (SimpleGraph.Walk.support_map _ _)
      _ = U.first.support.map Subtype.val := by
        rw [hPs,List.map_map]
        rfl
      _ = trace.map Subtype.val := by
        change (O.paths.first.mapLe (openGraph_le _ C)).support.map Subtype.val=_
        rw [SimpleGraph.Walk.support_mapLe_eq_support,O.first_support]
  have hsource : ∀ z ∈ P.support, z ∈ PD.FK.latticeRectangle (0,0) (2*n) (2*n) := by
    intro z hz
    rw [hPS] at hz
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
    exact v.property
  have hfirstP : firstContactTrace {z | z.1=4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.2} P.support=some P.support := by
    rw [hPS,firstContactTrace_map_of_target_iff Subtype.val
      {v : PrefixSourceVertex n | v.val.1=4*(s:ℤ)-1 ∧ b.2.val.2 ≤ v.val.2}
      {z | z.1=4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.2} (fun _ => Iff.rfl),hfirst]
    rfl
  have htipP : (4*(s:ℤ),b.2.val.2) ∉ P.support := by
    intro hmem
    have hD : P.support=D.first.support.map Subtype.val :=
      (SimpleGraph.Walk.support_copy _ _ _).trans (SimpleGraph.Walk.support_map _ _)
    rw [hD] at hmem
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp hmem
    exact D.first_support_not_beta (by omega) hy v hv
      (Or.inr (Or.inr (by rw [heq]; exact ⟨rfl,le_rfl⟩)))
  let pAux := p.map (prefixPaddingOpenHom n s hfit b C)
  let pLattice := pAux.map (rectangleOpenGraphToSquare (0,0) (2*n+1) (2*n+1)
    (prefixAuxCompletion n s hfit b C))
  have hAuxS : pLattice.support=trace.map Subtype.val := by
    rw [SimpleGraph.Walk.support_map]
    change (p.map (prefixPaddingOpenHom n s hfit b C)).support.map Subtype.val=_
    rw [SimpleGraph.Walk.support_map,List.map_map]
    change p.support.map Subtype.val=_
    rw [hp]
  have hEdges : P.edges=pLattice.edges := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support,SimpleGraph.Walk.edges_eq_zipWith_support,hPS,hAuxS]
  have htrace : ∀ f : (prefixAuxGraph n).edgeSet,
      (rectanglePrimalEdgeBond (0,0) (2*n+1) (2*n+1) f).toSym2 ∈ P.edges →
      f ∈ prefixAuxCompletion n s hfit b C := by
    intro f hf
    apply PlanarTopology.rectangle_open_walk_trace_subset (0,0) (2*n+1) (2*n+1) _ pAux
    apply (PlanarTopology.mem_rectangleTraceConfiguration _ _ _ pLattice f).mpr
    rw [←hEdges]
    exact (rectanglePrimalEdgeBond_toSym2_public (0,0) (2*n+1) (2*n+1) f) ▸ hf
  obtain ⟨L,hallowed,hα,hβ,hsupport⟩ := crosscut_left_barrier_indices_with_support M
    (4*(s:ℤ)) b.2.val.2 (by dsimp [M]; omega) hy
    (by have hh := ((PD.FK.mem_latticeRectangle _ _ _ _).mp b.2.property).2.2; dsimp [M] at *; omega) D
  have hopen := prefixAux_barrier_trace_open n s M hfit b C (by dsimp [M]; omega)
    (by dsimp [M]; omega) (by dsimp [M]; omega) D.firstStart.val.1 D.firstEnd.val.2 P htipP htrace L hallowed
  have hendpoint := raw_left_source_query_endpoints_of_barrier n M (4*(s:ℤ)) b.2.val.2
    D.firstStart.val.1 D.firstEnd.val.2 (by dsimp [M]; omega) hx D.first_start_right hxw
    (by dsimp [M]; omega) (by dsimp [M]; omega) (by dsimp [M]; omega)
    D.first_end_height (by have hh := ((PD.FK.mem_latticeRectangle _ _ _ _).mp b.2.property).2.2; dsimp at hh; omega)
    P hsource hfirstP L hallowed hα hβ hsupport _ hopen e he u hu
  have hcut : sourceCoordinateTrace (2*n) (2*n) {z | z ∈ P.support} =
      sourceCoordinateTrace (2*n) (2*n) (Subtype.val '' {z | z ∈ trace}) := by
    ext v
    change v.val ∈ P.support ↔ ∃ z, z ∈ trace ∧ z.val=v.val
    rw [hPS,List.mem_map]
  exact hcut ▸ hendpoint

/-- The inspected variable bonds lie in the exact source stopped reveal
for every attained tip and every physical confined first-contact prefix. -/
theorem actual_confined_prefix_query_subset_stoppedReveal
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s) (trace : List (PrefixSourceVertex n))
    (hb : caseTwoTipEndpointSelector n s hfit C=some b)
    (hpath : ConfinedPrefixFirstContact n s hfit C b trace) :
    paddedPrefixSourceQueryReveal n s hfit b C ⊆ caseTwoStoppedPrefixReveal n s hfit b trace := by
  classical
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
  have hraw := (Finset.mem_filter.mp hf).2.1
  let e := embeddedEdgeEmbedding _ _ (Function.Embedding.refl _)
    (caseTwoConfinedPrefixGraph_map_le n s hfit b) f
  have hcomp : embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n)
      (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (prefix_padding_rectangle_subset n)) e =
    embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n) (confinedPrefix_padding_map_le n s hfit b) f := by
    apply Subtype.ext
    have h1 := embeddedEdgeEmbedding_coe _ _ (prefixPaddingEmbedding n)
      (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (prefix_padding_rectangle_subset n)) e
    have h2 := embeddedEdgeEmbedding_coe _ _ (prefixPaddingEmbedding n)
      (confinedPrefix_padding_map_le n s hfit b) f
    have hecoe : e.val=f.val :=
      (embeddedEdgeEmbedding_coe _ _ (Function.Embedding.refl _)
        (caseTwoConfinedPrefixGraph_map_le n s hfit b) f).trans (by
          change Sym2.map id f.val=f.val
          exact congrFun Sym2.map_id f.val)
    exact h1.trans ((congrArg (fun z => (prefixPaddingEmbedding n).sym2Map z) hecoe).trans h2.symm)
  have heaux : embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n)
      (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (prefix_padding_rectangle_subset n)) e ∈
      intervalArmLeftReveal (2*n+1) (4*(s:ℤ)) (prefixAuxCompletion n s hfit b C) := hcomp.symm ▸ hraw
  have hend : ∀ u ∈ e.val, u ∈ pocketAugmentedSourceLeftExterior (2*n) (2*n) (4*(s:ℤ)) b.2.val.2
      (sourceCoordinateTrace (2*n) (2*n) (Subtype.val '' {z | z ∈ trace})) :=
    fun u hu => actual_confined_prefix_raw_query_endpoint_left n s hs hfit C b trace hb hpath e heaux u hu
  change e ∈ pocketAugmentedSourceReveal (2*n) (2*n) (4*(s:ℤ)) b.2.val.2
    (Subtype.val '' {z | z ∈ trace}) (Subtype.val '' {z | z ∈ caseTwoTipOriginalTrace n s hfit b.1})
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  let v := e.val.out.1
  let w := e.val.out.2
  have hepair : s(v,w)=e.val := Quot.out_eq _
  have hadj : (rectangleGraph (0,0) (2*n) (2*n)).Adj v w :=
    (rectangleGraph (0,0) (2*n) (2*n)).mem_edgeSet.mp (hepair.symm ▸ e.property)
  have hee : e=(⟨s(v,w),(rectangleGraph (0,0) (2*n) (2*n)).mem_edgeSet.mpr hadj⟩ :
      (rectangleGraph (0,0) (2*n) (2*n)).edgeSet) := Subtype.ext hepair.symm
  have hv := hend v (hepair ▸ Sym2.mem_mk_left v w)
  have hw := hend w (hepair ▸ Sym2.mem_mk_right v w)
  exact hee.symm ▸ (mem_internalBonds_pair _ _ v w hadj).mpr ⟨hv,hw⟩

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
