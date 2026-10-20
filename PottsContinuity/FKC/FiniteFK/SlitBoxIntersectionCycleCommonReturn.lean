-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxIntersectionCycleCommonReturn.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCommonExteriorReturn
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateExteriorNeighbors
public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateIntersectionCycleUnion
public import PottsContinuity.FKC.Medial.CycleDegreeTwoPropagation

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open SimpleGraph

private theorem cycle_neighbor_eq_of_containing_degree_two
    {V : Type*} {G₀ G : SimpleGraph V} {u : V}
    (c : G₀.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe ≤ G)
    {x : V} (hx : x ∈ c.support)
    (hdeg : (G.neighborSet x).ncard = 2) :
    G.neighborSet x = c.toSubgraph.spanningCoe.neighborSet x := by
  classical
  let C := c.toSubgraph.spanningCoe
  have hsub : C.neighborSet x ⊆ G.neighborSet x :=
    SimpleGraph.neighborSet_mono hspan x
  have hCcard : (C.neighborSet x).ncard = 2 := by
    change (c.toSubgraph.neighborSet x).ncard = 2
    exact hc.ncard_neighborSet_toSubgraph_eq_two hx
  have hpos : 0 < (G.neighborSet x).ncard := by rw [hdeg]; omega
  have hfinite : (G.neighborSet x).Finite := Set.finite_of_ncard_pos hpos
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ hfinite).symm
  rw [hCcard, hdeg]

private theorem simpleWalk_edges_in_cycle_of_restricted_degree
    {V : Type*} {G₀ G : SimpleGraph V} {u : V}
    (c : G₀.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe ≤ G)
    {a b : V} (r : G₀.Walk a b) (hr : r.IsPath)
    (ha : a ∈ c.support)
    (hedges : ∀ e ∈ r.edges, e ∈ G.edgeSet)
    (hdeg : ∀ x ∈ r.support, x ≠ b → (G.neighborSet x).ncard = 2) :
    b ∈ c.support ∧ ∀ e ∈ r.edges, e ∈ c.edges := by
  classical
  induction r with
  | nil => exact ⟨ha, by simp⟩
  | @cons x y z hxy tail ih =>
      have hpath := (SimpleGraph.Walk.cons_isPath_iff hxy tail).mp hr
      have hxnot : x ∉ tail.support := hpath.2
      have hxne : x ≠ z := by intro h; subst z; exact hxnot (by simp)
      have hxmem : x ∈ (Walk.cons hxy tail).support := by simp
      have hdegx := hdeg x hxmem hxne
      have hneighbors := cycle_neighbor_eq_of_containing_degree_two c hc hspan ha hdegx
      have hedge : s(x,y) ∈ G.edgeSet := hedges (s(x,y)) (by simp)
      have hadjG : G.Adj x y := G.mem_edgeSet.mp hedge
      have hyG : y ∈ G.neighborSet x := (G.mem_neighborSet x y).mpr hadjG
      have hyC : y ∈ c.toSubgraph.spanningCoe.neighborSet x := by rw [← hneighbors]; exact hyG
      have hxyC : c.toSubgraph.spanningCoe.Adj x y :=
        (c.toSubgraph.spanningCoe.mem_neighborSet x y).mp hyC
      have hysupport : y ∈ c.support :=
        c.mem_verts_toSubgraph.mp (c.toSubgraph.edge_vert hxyC.symm)
      have htailEdges : ∀ e ∈ tail.edges, e ∈ G.edgeSet := by
        intro e he
        exact hedges e (by simp [he])
      have htailDeg : ∀ x' ∈ tail.support, x' ≠ z →
          (G.neighborSet x').ncard = 2 := by
        intro x' hx' hx'z
        exact hdeg x' (by simp [hx']) hx'z
      obtain ⟨hzsupport, htailC⟩ := ih hpath.1 hysupport htailEdges htailDeg
      refine ⟨hzsupport, ?_⟩
      intro e he
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact (SimpleGraph.Walk.mem_edges_toSubgraph c).mp
          ((c.toSubgraph).mem_edgeSet.mpr hxyC)
      · exact htailC e he


private theorem walk_support_subset_of_edges_subset
    {V : Type*} {G H : SimpleGraph V} {a b c d : V}
    (w : G.Walk a b) (v : H.Walk c d) (hnil : ¬ w.Nil)
    (hsub : ∀ e ∈ w.edges, e ∈ v.edges) :
    ∀ x ∈ w.support, x ∈ v.support := by
  intro x hx
  obtain ⟨e, he, hxe⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hx
  have hev := hsub e he
  rcases Sym2.mk_surjective e with ⟨⟨y,z⟩, rfl⟩
  have hxe' : x = y ∨ x = z := by simpa using hxe
  rcases hxe' with rfl | rfl
  · exact v.fst_mem_support_of_mem_edges hev
  · exact v.snd_mem_support_of_mem_edges hev



def intersectionCandidateAllOpenHom (n : ℕ)
    (A : Configuration (slitBoxGraph n)) [Fintype (slitBoxGraph n).edgeSet
    ] (hA : A = Finset.univ) :
    slitBoxGraph n →g openGraph (slitBoxGraph n) A where
  toFun := id
  map_rel' := by
    intro x y hxy
    apply (openGraph_adj (slitBoxGraph n) A x y).2
    change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
    rw [hA]
    refine ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩, ?_, rfl⟩
    exact Finset.mem_univ _

theorem slitBoxFirstHitIntersectionCycle_contains_canonical_top_return
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p q : SlitBoxFirstHitBaseCandidates n u)
    {z : LatticeVertex} (c : squareLattice.Walk z z) (hc : c.IsCycle)
    (hcommon : s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ c.edges)
    (hboundary : ∀ e ∈ c.edges,
      e ∈ (latticeCellBoundaryGraph
        ((slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ∩
          (slitBoxFirstHitCandidatePolygon n hn u huY huX q).interiorCellBases δ)).edgeSet) :
    (slitBoxTopArcVertex n).val ∈ c.support ∧ u.val ∈ c.support ∧
      ∀ e ∈ (slitBoxCanonicalReturnWalk n u huY huX
        (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).edges,
        e ∈ c.edges := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let f := intersectionCandidateAllOpenHom n A hA
  let t := p.val.1
  let prewalk := (((p.val.2 : (slitBoxGraph n).Walk u t).map f).map
    (slitBoxOpenGraphToSquareLatticeHom n A))
  let pret := slitBoxCanonicalReturnWalk n u huY huX t p.property.1
  let cp := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let cq := slitBoxFirstHitCandidateCycle n hn u huY huX q
  let U := cp.toSubgraph.spanningCoe ⊔ cq.toSubgraph.spanningCoe
  let R := slitBoxCanonicalReturnWalk n u huY huX
    (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)
  let seed : LatticeVertex := ((n + 1 : ℤ), 0)
  have hRpath : R.IsPath := by
    exact slitBoxCanonicalTopReturnWalk_isPath n hn u huY huX
  have hRright : s(((n + 1 : ℤ), 0), ((n + 1 : ℤ), 1)) ∈ R.edges := by
    exact slitBoxCanonicalTopReturnWalk_right_edge_mem n hn u huY huX
  have hseedR : seed ∈ R.support := by
    exact R.fst_mem_support_of_mem_edges (by simpa [seed] using hRright)
  have hseedC : seed ∈ c.support := by
    exact c.fst_mem_support_of_mem_edges (by simpa [seed] using hcommon)
  have hcpEq : cp = prewalk.append pret := by
    dsimp [cp, prewalk, pret, f, t, A, hA, slitBoxFirstHitCandidateCycle,
      intersectionCandidateAllOpenHom]
    rfl
  have hRcp : ∀ e ∈ R.edges, e ∈ cp.edges := by
    intro e he
    have hret := slitBoxCanonicalTopReturnWalk_edges_subset_any_arc_return
      n u huY huX p.val.1 p.property.1 e he
    rw [hcpEq]
    have hEdgesEq : (prewalk.append pret).edges = prewalk.edges ++ pret.edges :=
      SimpleGraph.Walk.edges_append prewalk pret
    exact hEdgesEq ▸ List.mem_append.mpr (Or.inr hret)
  have hstartEnd : (slitBoxTopArcVertex n).val ≠ u.val := by
    intro heq
    have hy := congrArg Prod.snd heq
    simp [slitBoxTopArcVertex] at hy
    omega
  have hRnonempty : ¬ R.Nil := SimpleGraph.Walk.not_nil_of_ne hstartEnd
  have hRsupportCp : ∀ x ∈ R.support, x ∈ cp.support := by
    apply walk_support_subset_of_edges_subset R cp hRnonempty hRcp
  have hcycleEdges := PottsContinuity.FKC.FiniteFK.slitBoxFirstHitCandidateIntersection_cycle_edges_subset_union
    n hn u huY huX δ p q c hc hboundary
  have hspan : c.toSubgraph.spanningCoe ≤ U := by
    rw [SimpleGraph.le_iff_adj]
    intro a b hab
    have heC : s(a,b) ∈ c.edges :=
      (SimpleGraph.Walk.mem_edges_toSubgraph c).mp
        ((c.toSubgraph).mem_edgeSet.mpr hab)
    have heUnion := hcycleEdges (s(a,b)) heC
    have heU : s(a,b) ∈ U.edgeSet := by
      rcases heUnion with heP | heQ
      · rw [SimpleGraph.edgeSet_sup]
        exact Set.mem_union_left _ <| by
          rw [SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.edgeSet_toSubgraph]
          exact SimpleGraph.Walk.mem_edgeSet.mpr heP
      · rw [SimpleGraph.edgeSet_sup]
        exact Set.mem_union_right _ <| by
          rw [SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.edgeSet_toSubgraph]
          exact SimpleGraph.Walk.mem_edgeSet.mpr heQ
    exact U.mem_edgeSet.mp heU
  have hRedgesU : ∀ e ∈ R.edges, e ∈ U.edgeSet := by
    intro e he
    have hecp := hRcp e he
    rw [SimpleGraph.edgeSet_sup]
    exact Set.mem_union_left _ <| by
      rw [SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.edgeSet_toSubgraph]
      exact SimpleGraph.Walk.mem_edgeSet.mpr hecp
  have hboxClass (x : LatticeVertex) (hx : x ∈ R.support)
      (hxbox : x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) :
      x = u.val ∨ x = (slitBoxTopArcVertex n).val := by
    simpa [slitBoxTopArcVertex] using
      slitBoxCanonicalTopReturnWalk_support_in_box n hn u huY huX
        (z := x) hx hxbox
  have huNeSeed : u.val ≠ seed := by
    intro heq
    have hy := congrArg Prod.snd heq
    simp [seed] at hy
    omega
  have hbottomNotTake : u.val ∉ (R.takeUntil seed hseedR).support := by
    apply SimpleGraph.Walk.endpoint_notMem_support_takeUntil hRpath hseedR
    exact huNeSeed
  have htopMemTake : (slitBoxTopArcVertex n).val ∈ (R.takeUntil seed hseedR).support := by
    simp [R]
  have hnodupSplit : ((R.takeUntil seed hseedR).support ++
      (R.dropUntil seed hseedR).support.tail).Nodup := by
    have h := hRpath.support_nodup
    rw [← SimpleGraph.Walk.take_spec R hseedR, SimpleGraph.Walk.support_append] at h
    exact h
  have htopNotDropTail : (slitBoxTopArcVertex n).val ∉
      (R.dropUntil seed hseedR).support.tail := by
    intro htopTail
    have hdisjoint := (List.nodup_append.mp hnodupSplit).2.2
      (slitBoxTopArcVertex n).val htopMemTake (slitBoxTopArcVertex n).val htopTail
    exact hdisjoint rfl
  have htopNotDrop : (slitBoxTopArcVertex n).val ∉
      (R.dropUntil seed hseedR).support := by
    intro hmem
    have hseedDrop : seed ∈ (R.dropUntil seed hseedR).support :=
      (R.dropUntil seed hseedR).start_mem_support
    have hcons : (R.dropUntil seed hseedR).support =
        seed :: (R.dropUntil seed hseedR).support.tail := by
      simp
    rw [hcons] at hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · have hcoords : (slitBoxTopArcVertex n).val = seed := heq
      have hy := congrArg Prod.snd hcoords
      simp [seed, slitBoxTopArcVertex] at hy
      omega
    · exact htopNotDropTail htail
  have hprewalk : (R.takeUntil seed hseedR).IsPath := hRpath.takeUntil hseedR
  have hsuffixPath : (R.dropUntil seed hseedR).IsPath := hRpath.dropUntil hseedR
  have hprewalkDegree : ∀ x ∈ (R.takeUntil seed hseedR).reverse.support,
      x ≠ (slitBoxTopArcVertex n).val → (U.neighborSet x).ncard = 2 := by
    intro x hx hxend
    have hxTake : x ∈ (R.takeUntil seed hseedR).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hx
    have hxR : x ∈ R.support :=
      SimpleGraph.Walk.support_takeUntil_subset_support R hseedR hxTake
    have hxNotBox : x ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
      intro hxbox
      rcases hboxClass x hxR hxbox with hxu | hxtop
      · exact hbottomNotTake (hxu ▸ hxTake)
      · exact hxend hxtop
    exact slitBoxFirstHitCandidateCycle_union_degree_two_of_outside
      n hn u huY huX p q hxNotBox (hRsupportCp x hxR)
  have hsuffixDegree : ∀ x ∈ (R.dropUntil seed hseedR).support,
      x ≠ u.val → (U.neighborSet x).ncard = 2 := by
    intro x hx hxend
    have hxR : x ∈ R.support :=
      SimpleGraph.Walk.support_dropUntil_subset_support R hseedR hx
    have hxNotBox : x ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
      intro hxbox
      rcases hboxClass x hxR hxbox with hxu | hxtop
      · exact hxend hxu
      · exact htopNotDrop (hxtop ▸ hx)
    exact slitBoxFirstHitCandidateCycle_union_degree_two_of_outside
      n hn u huY huX p q hxNotBox (hRsupportCp x hxR)
  have hprewalkReverse : (R.takeUntil seed hseedR).reverse.IsPath :=
    SimpleGraph.Walk.isPath_reverse_iff _ |>.mpr hprewalk
  have hprewalkEdgesU : ∀ e ∈ (R.takeUntil seed hseedR).reverse.edges, e ∈ U.edgeSet := by
    intro e he
    apply hRedgesU e
    have hs := SimpleGraph.Walk.edges_takeUntil_subset_edges R hseedR
    have heTake : e ∈ (R.takeUntil seed hseedR).edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using he
    exact hs heTake
  have hprewalkResult := simpleWalk_edges_in_cycle_of_restricted_degree c hc hspan
    (R.takeUntil seed hseedR).reverse hprewalkReverse hseedC hprewalkEdgesU hprewalkDegree
  have hsuffixEdgesU : ∀ e ∈ (R.dropUntil seed hseedR).edges, e ∈ U.edgeSet := by
    intro e he
    exact hRedgesU e (SimpleGraph.Walk.edges_dropUntil_subset_edges R hseedR he)
  have hsuffixResult := simpleWalk_edges_in_cycle_of_restricted_degree c hc hspan
    (R.dropUntil seed hseedR) hsuffixPath hseedC hsuffixEdgesU hsuffixDegree
  have htopC : (slitBoxTopArcVertex n).val ∈ c.support := by
    exact hprewalkResult.1
  have huC : u.val ∈ c.support := by exact hsuffixResult.1
  refine ⟨htopC, huC, ?_⟩
  intro e he
  have htake := SimpleGraph.Walk.edges_takeUntil_subset_edges R hseedR
  have hdrop := SimpleGraph.Walk.edges_dropUntil_subset_edges R hseedR
  have hdecomp : (R.takeUntil seed hseedR).edges ++ (R.dropUntil seed hseedR).edges = R.edges := by
    have h := congrArg SimpleGraph.Walk.edges (SimpleGraph.Walk.take_spec R hseedR)
    simpa only [SimpleGraph.Walk.edges_append] using h
  rw [← hdecomp] at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · have he' : e ∈ (R.takeUntil seed hseedR).reverse.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using he
    have hc' := hprewalkResult.2 e he'
    simpa [SimpleGraph.Walk.edges_reverse] using hc'
  · exact hsuffixResult.2 e he

end PottsContinuity.FKC.FiniteFK

