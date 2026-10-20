-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonCellBoundaryGraph.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryCriterion
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle
public import PottsContinuity.FKC.Domains.LatticeCellBoundary
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open SimpleGraph

noncomputable section

theorem mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond
    {m : ℕ} (P : LatticePolygon m) (δ : PositiveMesh) (e : LatticeBond) :
    e ∈ latticeCellBoundaryBonds (P.interiorCellBases δ) ↔
      ∃ i : ZMod (m + 3), e = P.boundaryBond i := by
  rw [mem_latticeCellBoundaryBonds]
  simpa only [P.mem_interiorCellBases_iff δ] using
    P.cellCenters_differ_iff_boundaryBond δ e

theorem latticeCellBoundaryGraph_interiorCellBases_eq_cycle
    {v : LatticeVertex} {p : squareLattice.Walk v v} (hp : p.IsCycle)
    (δ : PositiveMesh) :
    latticeCellBoundaryGraph ((latticePolygonOfCycle hp).interiorCellBases δ) =
      p.toSubgraph.spanningCoe := by
  let P := latticePolygonOfCycle hp
  have hlen : p.length - 3 + 3 = p.length := by
    have h3 := hp.three_le_length
    omega
  let : Fact (1 < p.length - 3 + 3) := ⟨by rw [hlen]; omega⟩
  ext a b
  rw [← (latticeCellBoundaryGraph (P.interiorCellBases δ)).mem_edgeSet,
    ← (p.toSubgraph.spanningCoe).mem_edgeSet]
  have hcycle : s(a,b) ∈ (p.toSubgraph.spanningCoe).edgeSet ↔ s(a,b) ∈ p.edges := by
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
  constructor
  · intro hboundary
    have hadj := (latticeCellBoundaryGraph_adj_iff _ a b).mp
      ((latticeCellBoundaryGraph _).mem_edgeSet.mp hboundary)
    obtain ⟨e, hpair, hedge⟩ := hadj.2
    have hedgeMem : e ∈ latticeCellBoundaryBonds (P.interiorCellBases δ) :=
      (mem_latticeCellBoundaryBonds _ _).mpr hedge
    obtain ⟨i, rfl⟩ :=
      (mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond P δ e).mp hedgeMem
    apply hcycle.mpr
    apply (latticePolygonOfCycle_edge_iff hp (s(a,b))).mpr
    refine ⟨i, ?_⟩
    have hsym : s(a,b) = (P.boundaryBond i).toSym2 := by
      simpa [LatticeBond.toSym2] using hpair.symm
    rw [P.boundaryBond_toSym2 i] at hsym
    simpa [P, latticePolygonOfCycle] using hsym
  · intro hedge
    have hedge' : s(a,b) ∈ p.edges := hcycle.mp hedge
    have hpoly := (latticePolygonOfCycle_edge_iff hp (s(a,b))).mp hedge'
    obtain ⟨i, hi⟩ := hpoly
    have hb := P.boundaryBond_toSym2 i
    have hface : ((P.boundaryBond i).faceBase true ∈ P.interiorCellBases δ) ≠
        ((P.boundaryBond i).faceBase false ∈ P.interiorCellBases δ) := by
      have hmem := (mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond P δ
        (P.boundaryBond i)).mpr ⟨i, rfl⟩
      exact (mem_latticeCellBoundaryBonds _ _).mp hmem
    have hAdj : (latticeCellBoundaryGraph (P.interiorCellBases δ)).Adj a b := by
      apply (latticeCellBoundaryGraph_adj_iff _ a b).mpr
      refine ⟨?_, P.boundaryBond i, ?_, hface⟩
      · have hstep : squareLattice.Adj (P.vertex i) (P.vertex (i+1)) := P.adjacent i
        have hpair : s(a,b) = s(P.vertex i, P.vertex (i+1)) := by
          exact hi
        rw [Sym2.eq_iff] at hpair
        rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hstep
        · exact hstep.symm
      · have hpair : s(a,b) = (P.boundaryBond i).toSym2 := by
          exact hi.trans hb.symm
        simpa [LatticeBond.toSym2] using hpair.symm
    exact (latticeCellBoundaryGraph (P.interiorCellBases δ)).mem_edgeSet.mpr hAdj

end
end PottsContinuity.FKC.LatticePolygon
