module

public import PottsContinuity.Exploration.ConnectedBoundaryInclusion
public import PottsContinuity.PD.Duality.CircuitEnclosure
public import PottsContinuity.Thm3.RSW.PolygonRayExterior
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph
public import PottsContinuity.FKC.Domains.LatticeCellBoundaryGraphFaithfulness
public import PottsContinuity.FKC.Domains.LatticePolygonCellConnectivity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! A finite connected set of lattice cells is contained in a simple cycle
whose crossed bonds lie on the cell boundary. -/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality
open PottsContinuity.FKC

noncomputable section

def pdBondToFkc (e : PD.FK.Medial.LatticeBond) : FKC.Medial.LatticeBond :=
  match e with
  | ⟨b, .horizontal⟩ => ⟨b, .horizontal⟩
  | ⟨b, .vertical⟩ => ⟨b, .vertical⟩

private theorem pdBondToFkc_faceBase_false (e : PD.FK.Medial.LatticeBond) :
    (pdBondToFkc e).faceBase false = e.faceBase false := by
  rcases e with ⟨b, axis⟩
  cases axis <;> rfl

private theorem pdBondToFkc_faceBase_true (e : PD.FK.Medial.LatticeBond) :
    (pdBondToFkc e).faceBase true = e.faceBase true := by
  rcases e with ⟨b, axis⟩
  cases axis <;> rfl

private theorem pdBondToFkc_toSym2 (e : PD.FK.Medial.LatticeBond) :
    (pdBondToFkc e).toSym2 = e.toSym2 := by
  rcases e with ⟨b, axis⟩
  cases axis <;> rfl

private theorem pdCellBoundary_adj_to_fkc (S : Finset PD.FK.LatticeVertex)
    {u v : PD.FK.LatticeVertex}
    (h : (PD.FK.latticeCellBoundaryGraph S).Adj u v) :
    (FKC.latticeCellBoundaryGraph S).Adj u v := by
  obtain ⟨hadj, e, heq, hdiff⟩ :=
    (PD.FK.latticeCellBoundaryGraph_adj_iff S u v).mp h
  apply (FKC.latticeCellBoundaryGraph_adj_iff S u v).mpr
  have hadj' : FKC.squareLattice.Adj u v :=
    (FKC.squareLattice_adj_iff _ _).mpr
      ((PD.FK.squareLattice_adj_iff _ _).mp hadj)
  refine ⟨hadj', pdBondToFkc e, ?_, ?_⟩
  · simpa [pdBondToFkc_toSym2] using heq
  · simpa [pdBondToFkc_faceBase_true, pdBondToFkc_faceBase_false] using hdiff

def fkcBondToPd (e : FKC.Medial.LatticeBond) : PD.FK.Medial.LatticeBond :=
  match e with
  | ⟨b, .horizontal⟩ => ⟨b, .horizontal⟩
  | ⟨b, .vertical⟩ => ⟨b, .vertical⟩

private theorem pdBondToFkc_fkcBondToPd (e : FKC.Medial.LatticeBond) :
    pdBondToFkc (fkcBondToPd e) = e := by
  rcases e with ⟨b, axis⟩
  cases axis <;> rfl

private theorem fkcBondToPd_faceBase_false (e : FKC.Medial.LatticeBond) :
    (fkcBondToPd e).faceBase false = e.faceBase false := by
  rw [← pdBondToFkc_faceBase_false (fkcBondToPd e), pdBondToFkc_fkcBondToPd]

private theorem fkcBondToPd_faceBase_true (e : FKC.Medial.LatticeBond) :
    (fkcBondToPd e).faceBase true = e.faceBase true := by
  rw [← pdBondToFkc_faceBase_true (fkcBondToPd e), pdBondToFkc_fkcBondToPd]

private theorem fkcBondToPd_toSym2 (e : FKC.Medial.LatticeBond) :
    (fkcBondToPd e).toSym2 = e.toSym2 := by
  rcases e with ⟨b, axis⟩
  cases axis <;> rfl

private theorem rayIndex_faceMark_eq_of_adjacent_cycleInterior
    {z : PD.FK.LatticeVertex} (p : PD.FK.squareLattice.Walk z z)
    (hp : p.IsCycle) (δ : FKC.PositiveMesh)
    {u v : FKC.LatticeVertex}
    (hu : u ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective
        (show Function.Injective PottsContinuity.RSW.polygonRayLatticeHom from
          fun _ _ h => h)).mpr hp)).interiorCellBases δ)
    (hv : v ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective
        (show Function.Injective PottsContinuity.RSW.polygonRayLatticeHom from
          fun _ _ h => h)).mpr hp)).interiorCellBases δ)
    (hadj : FKC.squareLattice.Adj u v) :
    PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark u) p =
      PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark v) p := by
  obtain ⟨d, hd⟩ := FKC.Medial.LatticeBond.exists_of_adj hadj
  let b := FKC.Medial.primalBondOfDual d
  have hfalse : b.faceBase false = d.source := by
    rw [← FKC.Medial.dualBondOfPrimal_source,
      FKC.Medial.dualBondOfPrimal_primalBondOfDual]
  have htrue : b.faceBase true = d.target := by
    rw [← FKC.Medial.dualBondOfPrimal_target,
      FKC.Medial.dualBondOfPrimal_primalBondOfDual]
  have hnot : b.toSym2 ∉ p.edges := by
    intro hmem
    have hdiff := (PottsContinuity.RSW.polygonRay_bond_mem_iff_cell_difference
      p hp b δ).mp hmem
    have hsourceTarget :
        (d.source = u ∧ d.target = v) ∨ (d.source = v ∧ d.target = u) := by
      change s(d.source, d.target) = s(u, v) at hd
      exact Sym2.eq_iff.mp hd
    rcases hsourceTarget with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · apply hdiff
      rw [htrue, hfalse, ht, hs]
      exact propext (by simp [hu, hv])
    · apply hdiff
      rw [htrue, hfalse, hs, ht]
      exact propext (by simp [hu, hv])
  have hnotPd : (fkcBondToPd b).toSym2 ∉ p.edges := by
    simpa [fkcBondToPd_toSym2] using hnot
  have hindexPd := PottsContinuity.Push.rayIndex_bond_faces_eq_of_not_mem
    p (fkcBondToPd b) hnotPd
  have hindex :
      PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark (b.faceBase false)) p =
        PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark (b.faceBase true)) p := by
    simpa [fkcBondToPd_faceBase_false, fkcBondToPd_faceBase_true,
      pdBondToFkc_fkcBondToPd] using hindexPd
  have hindexD :
      PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark d.source) p =
        PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark d.target) p := by
    rw [← hfalse, ← htrue]
    exact hindex
  have hsourceTarget :
      (d.source = u ∧ d.target = v) ∨ (d.source = v ∧ d.target = u) := by
    change s(d.source, d.target) = s(u, v) at hd
    exact Sym2.eq_iff.mp hd
  rcases hsourceTarget with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · simpa [hs, ht] using hindexD
  · simpa [hs, ht] using hindexD.symm

private theorem rayIndex_faceMark_eq_of_connected_cycleInterior
    {z : PD.FK.LatticeVertex} (p : PD.FK.squareLattice.Walk z z)
    (hp : p.IsCycle) (δ : FKC.PositiveMesh)
    {u v : FKC.LatticeVertex}
    (hu : u ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective
        (show Function.Injective PottsContinuity.RSW.polygonRayLatticeHom from
          fun _ _ h => h)).mpr hp)).interiorCellBases δ)
    (hv : v ∈ (FKC.latticePolygonOfCycle
      ((p.isCycle_map_iff_of_injective
        (show Function.Injective PottsContinuity.RSW.polygonRayLatticeHom from
          fun _ _ h => h)).mpr hp)).interiorCellBases δ) :
    PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark u) p =
      PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark v) p := by
  let r := p.map PottsContinuity.RSW.polygonRayLatticeHom
  have hr : r.IsCycle :=
    (p.isCycle_map_iff_of_injective
      (show Function.Injective PottsContinuity.RSW.polygonRayLatticeHom
        from fun _ _ h => h)).mpr hp
  let P := FKC.latticePolygonOfCycle hr
  let S := P.interiorCellBases δ
  have huS : u ∈ S := by simpa [S, P, r] using hu
  have hvS : v ∈ S := by simpa [S, P, r] using hv
  have hconnected : (FKC.squareLattice.induce (↑S : Set FKC.LatticeVertex)).Connected :=
    FKC.LatticePolygon.interiorCellBases_connected_of_cycle hr δ
  obtain ⟨w⟩ := hconnected.preconnected ⟨u, huS⟩ ⟨v, hvS⟩
  have hwalk : ∀ {a b : {x : FKC.LatticeVertex // x ∈ S}}
      (w : (FKC.squareLattice.induce (↑S : Set FKC.LatticeVertex)).Walk a b),
      PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark a.val) p =
        PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark b.val) p := by
    intro a b w
    induction w with
    | nil => rfl
    | @cons a b c hadj tail ih =>
      exact (rayIndex_faceMark_eq_of_adjacent_cycleInterior p hp δ
        a.property b.property hadj).trans ih
  exact hwalk w

/-- A finite connected cell set lies in the actual filling of one simple
boundary cycle, and every edge of the cycle remains on the original boundary. -/
theorem connected_cell_set_has_boundary_cycle_envelope
    (S : Finset PD.FK.LatticeVertex)
    (hconnected :
      (FKC.squareLattice.induce (↑S : Set FKC.LatticeVertex)).Connected)
    (hne : S.Nonempty) (δ : FKC.PositiveMesh) :
    ∃ z : PD.FK.LatticeVertex, ∃ p : PD.FK.squareLattice.Walk z z,
      ∃ hp : p.IsCycle,
        ∃ x ∈ S, PD.Duality.rayIndex
          (PottsContinuity.Push.faceIndexMark x) p ≠ 0 ∧
        S ⊆ (FKC.latticePolygonOfCycle
          ((p.isCycle_map_iff_of_injective
            (show Function.Injective RSW.polygonRayLatticeHom from
              fun _ _ h => h)).mpr hp)).interiorCellBases δ ∧
        ∀ e ∈ p.edges, e ∈ (FKC.latticeCellBoundaryGraph S).edgeSet := by
  classical
  obtain ⟨x, hxS, z, c, hc, hindex⟩ :=
    PD.Duality.cellBoundary_outer_cycle_nonzero S hne
  let p := c.mapLe (PD.FK.latticeCellBoundaryGraph_le S)
  have hp : p.IsCycle := hc.mapLe (PD.FK.latticeCellBoundaryGraph_le S)
  have hedgeOnS : ∀ e ∈ p.edges, e ∈ (FKC.latticeCellBoundaryGraph S).edgeSet := by
    intro e he
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he
    obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
    have hadj : (PD.FK.latticeCellBoundaryGraph S).Adj a b := c.adj_of_mem_edges he
    exact (FKC.latticeCellBoundaryGraph S).mem_edgeSet.mpr (pdCellBoundary_adj_to_fkc S hadj)
  let r := p.map RSW.polygonRayLatticeHom
  have hr : r.IsCycle :=
    (p.isCycle_map_iff_of_injective
      (show Function.Injective RSW.polygonRayLatticeHom from fun _ _ h => h)).mpr hp
  let P := FKC.latticePolygonOfCycle hr
  let T := P.interiorCellBases δ
  have hcycleGraph : FKC.latticeCellBoundaryGraph T = r.toSubgraph.spanningCoe := by
    simpa [T, P] using FKC.LatticePolygon.latticeCellBoundaryGraph_interiorCellBases_eq_cycle hr δ
  have hgraph : FKC.latticeCellBoundaryGraph T ≤ FKC.latticeCellBoundaryGraph S := by
    intro a b hab
    have hedgeT : s(a, b) ∈ (FKC.latticeCellBoundaryGraph T).edgeSet :=
      (FKC.latticeCellBoundaryGraph T).mem_edgeSet.mpr hab
    rw [hcycleGraph] at hedgeT
    have hedgeR : s(a, b) ∈ r.edges := by
      have hiff : s(a, b) ∈ r.toSubgraph.spanningCoe.edgeSet ↔ s(a, b) ∈ r.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      exact hiff.mp hedgeT
    have hedgeP : s(a, b) ∈ p.edges := by
      have hmap : r.edges = p.edges := by
        rw [SimpleGraph.Walk.edges_map]
        change List.map (Sym2.map id) p.edges = p.edges
        simp only [Sym2.map_id, List.map_id]
      rw [hmap] at hedgeR
      exact hedgeR
    exact (FKC.latticeCellBoundaryGraph S).mem_edgeSet.mp (hedgeOnS (s(a, b)) hedgeP)
  have hboundary : FKC.latticeCellBoundaryBonds T ⊆ FKC.latticeCellBoundaryBonds S :=
    (FKC.latticeCellBoundaryGraph_le_iff T S).mp hgraph
  have hxindex : PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark x) p ≠ 0 := by
    simpa [PottsContinuity.Push.faceIndexMark, p] using hindex
  have hxDomain : FKC.latticeCellCenter δ x ∈ P.domain δ :=
    PottsContinuity.RSW.polygonRay_cellCenter_mem_domain_of_ne_zero
      p hp δ x hxindex
  have hxT : x ∈ T := (P.mem_interiorCellBases_iff δ x).2 hxDomain
  have hsubset : S ⊆ T :=
    latticeCellSet_subset_of_connected_of_boundary_inclusion S T hconnected x hxS hxT hboundary
  refine ⟨z, p, hp, x, hxS, ?_, ?_, ?_⟩
  · simpa [PottsContinuity.Push.faceIndexMark, p] using hindex
  · simpa [T, P, r] using hsubset
  · exact hedgeOnS

/-- Two simple cycles with a common interior cell yield an outer boundary
cycle containing both fillings, with crossed edges in their combined support. -/
theorem two_cycle_union_has_boundary_cycle_envelope
    {z w : PD.FK.LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z) (q : PD.FK.squareLattice.Walk w w)
    (hp : p.IsCycle) (hq : q.IsCycle) (δ : FKC.PositiveMesh)
    (x : FKC.LatticeVertex)
    (hxP : PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark x) p ≠ 0)
    (hxQ : PD.Duality.rayIndex (PottsContinuity.Push.faceIndexMark x) q ≠ 0) :
    ∃ z' : PD.FK.LatticeVertex, ∃ c : PD.FK.squareLattice.Walk z' z',
      ∃ hc : c.IsCycle,
        (FKC.latticePolygonOfCycle
          ((p.isCycle_map_iff_of_injective
            (show Function.Injective RSW.polygonRayLatticeHom from
              fun _ _ h => h)).mpr hp)).interiorCellBases δ ∪
        (FKC.latticePolygonOfCycle
          ((q.isCycle_map_iff_of_injective
            (show Function.Injective RSW.polygonRayLatticeHom from
              fun _ _ h => h)).mpr hq)).interiorCellBases δ ⊆
          (FKC.latticePolygonOfCycle
            ((c.isCycle_map_iff_of_injective
              (show Function.Injective RSW.polygonRayLatticeHom from
                fun _ _ h => h)).mpr hc)).interiorCellBases δ ∧
        (∀ y, PD.Duality.rayIndex y p ≠ 0 → PD.Duality.rayIndex y c ≠ 0) ∧
        (∀ y, PD.Duality.rayIndex y q ≠ 0 → PD.Duality.rayIndex y c ≠ 0) ∧
        ∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges := by
  classical
  let rp := p.map RSW.polygonRayLatticeHom
  let rq := q.map RSW.polygonRayLatticeHom
  have hrp : rp.IsCycle :=
    (p.isCycle_map_iff_of_injective
      (show Function.Injective RSW.polygonRayLatticeHom from fun _ _ h => h)).mpr hp
  have hrq : rq.IsCycle :=
    (q.isCycle_map_iff_of_injective
      (show Function.Injective RSW.polygonRayLatticeHom from fun _ _ h => h)).mpr hq
  let Pp := FKC.latticePolygonOfCycle hrp
  let Pq := FKC.latticePolygonOfCycle hrq
  let Sp := Pp.interiorCellBases δ
  let Sq := Pq.interiorCellBases δ
  have hxSp : x ∈ Sp := by
    apply (Pp.mem_interiorCellBases_iff δ x).2
    exact PottsContinuity.RSW.polygonRay_cellCenter_mem_domain_of_ne_zero
      p hp δ x hxP
  have hxSq : x ∈ Sq := by
    apply (Pq.mem_interiorCellBases_iff δ x).2
    exact PottsContinuity.RSW.polygonRay_cellCenter_mem_domain_of_ne_zero
      q hq δ x hxQ
  have hSp : (FKC.squareLattice.induce (↑Sp : Set FKC.LatticeVertex)).Connected :=
    FKC.LatticePolygon.interiorCellBases_connected_of_cycle hrp δ
  have hSq : (FKC.squareLattice.induce (↑Sq : Set FKC.LatticeVertex)).Connected :=
    FKC.LatticePolygon.interiorCellBases_connected_of_cycle hrq δ
  have hUnion :
      (FKC.squareLattice.induce (↑(Sp ∪ Sq) : Set FKC.LatticeVertex)).Connected :=
    induced_cell_union_connected Sp Sq hSp hSq x hxSp hxSq
  obtain ⟨z', c, hc, anchor, hanchorS, hanchorIndex, hfill, hboundary⟩ :=
    connected_cell_set_has_boundary_cycle_envelope (Sp ∪ Sq) hUnion
      ⟨x, Finset.mem_union_left Sq hxSp⟩ δ
  have hcycleGraphP : FKC.latticeCellBoundaryGraph Sp = rp.toSubgraph.spanningCoe := by
    simpa [Sp, Pp, rp] using
      FKC.LatticePolygon.latticeCellBoundaryGraph_interiorCellBases_eq_cycle hrp δ
  have hcycleGraphQ : FKC.latticeCellBoundaryGraph Sq = rq.toSubgraph.spanningCoe := by
    simpa [Sq, Pq, rq] using
      FKC.LatticePolygon.latticeCellBoundaryGraph_interiorCellBases_eq_cycle hrq δ
  let rc := c.map RSW.polygonRayLatticeHom
  have hrc : rc.IsCycle :=
    (c.isCycle_map_iff_of_injective
      (show Function.Injective RSW.polygonRayLatticeHom from fun _ _ h => h)).mpr hc
  let Pc := FKC.latticePolygonOfCycle hrc
  let Sc := Pc.interiorCellBases δ
  have hanchorSc : anchor ∈ Sc := hfill hanchorS
  have hrpEdges : rp.edges = p.edges := by
    rw [SimpleGraph.Walk.edges_map]
    change List.map (Sym2.map id) p.edges = p.edges
    simp only [Sym2.map_id, List.map_id]
  have hrqEdges : rq.edges = q.edges := by
    rw [SimpleGraph.Walk.edges_map]
    change List.map (Sym2.map id) q.edges = q.edges
    simp only [Sym2.map_id, List.map_id]
  have hboundaryUnion :
      FKC.latticeCellBoundaryBonds (Sp ∪ Sq) ⊆
        FKC.latticeCellBoundaryBonds Sp ∪ FKC.latticeCellBoundaryBonds Sq :=
    FKC.latticeCellBoundaryBonds_subset_union Sp Sq
  have hsupport : ∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges := by
    intro e he
    obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
    have hedgeUnion : s(a, b) ∈
        (FKC.latticeCellBoundaryGraph (Sp ∪ Sq)).edgeSet := hboundary (s(a, b)) he
    have hadjUnion := (FKC.latticeCellBoundaryGraph (Sp ∪ Sq)).mem_edgeSet.mp hedgeUnion
    obtain ⟨hadj, d, hd, hdiff⟩ :=
      (FKC.latticeCellBoundaryGraph_adj_iff (Sp ∪ Sq) a b).mp hadjUnion
    have hdUnion : d ∈ FKC.latticeCellBoundaryBonds (Sp ∪ Sq) :=
      (FKC.mem_latticeCellBoundaryBonds _ _).mpr hdiff
    rcases Finset.mem_union.mp (hboundaryUnion hdUnion) with hdP | hdQ
    · have hdiffP := (FKC.mem_latticeCellBoundaryBonds Sp d).mp hdP
      have hadjP : (FKC.latticeCellBoundaryGraph Sp).Adj a b :=
        (FKC.latticeCellBoundaryGraph_adj_iff Sp a b).mpr ⟨hadj, d, hd, hdiffP⟩
      have hedgeP : s(a, b) ∈ rp.toSubgraph.spanningCoe.edgeSet := by
        rw [← hcycleGraphP]
        exact (FKC.latticeCellBoundaryGraph Sp).mem_edgeSet.mpr hadjP
      have hiffP : s(a, b) ∈ rp.toSubgraph.spanningCoe.edgeSet ↔ s(a, b) ∈ rp.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      have hP : s(a, b) ∈ rp.edges := hiffP.mp hedgeP
      rw [hrpEdges] at hP
      exact Or.inl hP
    · have hdiffQ := (FKC.mem_latticeCellBoundaryBonds Sq d).mp hdQ
      have hadjQ : (FKC.latticeCellBoundaryGraph Sq).Adj a b :=
        (FKC.latticeCellBoundaryGraph_adj_iff Sq a b).mpr ⟨hadj, d, hd, hdiffQ⟩
      have hedgeQ : s(a, b) ∈ rq.toSubgraph.spanningCoe.edgeSet := by
        rw [← hcycleGraphQ]
        exact (FKC.latticeCellBoundaryGraph Sq).mem_edgeSet.mpr hadjQ
      have hiffQ : s(a, b) ∈ rq.toSubgraph.spanningCoe.edgeSet ↔ s(a, b) ∈ rq.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      have hQ : s(a, b) ∈ rq.edges := hiffQ.mp hedgeQ
      rw [hrqEdges] at hQ
      exact Or.inr hQ
  have hrayP : ∀ y, PD.Duality.rayIndex y p ≠ 0 → PD.Duality.rayIndex y c ≠ 0 := by
    intro y hy
    let a : FKC.LatticeVertex := (y.1 - 1, y.2 - 1)
    have hmark : PottsContinuity.Push.faceIndexMark a = y := by
      simp [a, PottsContinuity.Push.faceIndexMark]
    have haDomain : FKC.latticeCellCenter δ a ∈ Pp.domain δ :=
      PottsContinuity.RSW.polygonRay_cellCenter_mem_domain_of_ne_zero
        p hp δ a (by simpa [hmark] using hy)
    have haP : a ∈ Sp := (Pp.mem_interiorCellBases_iff δ a).2 haDomain
    have haC : a ∈ Sc := hfill (Finset.mem_union_left Sq haP)
    have hindex := rayIndex_faceMark_eq_of_connected_cycleInterior
      c hc δ (u := anchor) (v := a) hanchorSc haC
    have hne : PD.Duality.rayIndex
        (PottsContinuity.Push.faceIndexMark a) c ≠ 0 := by
      rw [← hindex]
      exact hanchorIndex
    simpa [hmark] using hne
  have hrayQ : ∀ y, PD.Duality.rayIndex y q ≠ 0 → PD.Duality.rayIndex y c ≠ 0 := by
    intro y hy
    let a : FKC.LatticeVertex := (y.1 - 1, y.2 - 1)
    have hmark : PottsContinuity.Push.faceIndexMark a = y := by
      simp [a, PottsContinuity.Push.faceIndexMark]
    have haDomain : FKC.latticeCellCenter δ a ∈ Pq.domain δ :=
      PottsContinuity.RSW.polygonRay_cellCenter_mem_domain_of_ne_zero
        q hq δ a (by simpa [hmark] using hy)
    have haQ : a ∈ Sq := (Pq.mem_interiorCellBases_iff δ a).2 haDomain
    have haC : a ∈ Sc := hfill (Finset.mem_union_right Sp haQ)
    have hindex := rayIndex_faceMark_eq_of_connected_cycleInterior
      c hc δ (u := anchor) (v := a) hanchorSc haC
    have hne : PD.Duality.rayIndex
        (PottsContinuity.Push.faceIndexMark a) c ≠ 0 := by
      rw [← hindex]
      exact hanchorIndex
    simpa [hmark] using hne
  refine ⟨z', c, hc, ?_, hrayP, hrayQ, hsupport⟩
  · simpa [Sp, Sq, Pp, Pq, Sc, Pc, rc] using hfill

end
end PottsContinuity.Exploration
