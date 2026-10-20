-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeCellBoundaryVertexStar.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticeCellBoundaryGraphFaithfulness
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Domains

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open PottsContinuity.FKC.LatticePolygon
open SimpleGraph

private theorem no_incident_boundary_bond
    (F : Finset LatticeVertex) (v : LatticeVertex)
    (hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj v w)
    (e : LatticeBond) (hincident : v = e.source ∨ v = e.target) :
    e ∉ latticeCellBoundaryBonds F := by
  intro he
  have hfaces := (mem_latticeCellBoundaryBonds F e).mp he
  have hadj : (latticeCellBoundaryGraph F).Adj e.source e.target :=
    (latticeCellBoundaryGraph_adj_iff F e.source e.target).2
      ⟨e.adjacent, e, rfl, hfaces⟩
  rcases hincident with hsource | htarget
  · subst v
    exact hNo e.target hadj
  · subst v
    exact hNo e.source hadj.symm

private theorem no_boundary_bond_implies_face_membership_agreement
    (F : Finset LatticeVertex) (e : LatticeBond)
    (he : e ∉ latticeCellBoundaryBonds F) :
    (e.faceBase true ∈ F) ↔ (e.faceBase false ∈ F) := by
  have hcolors : ¬ ((e.faceBase true ∈ F) ≠ (e.faceBase false ∈ F)) := by
    intro h
    exact he ((mem_latticeCellBoundaryBonds F e).mpr h)
  exact Iff.of_eq (not_ne_iff.mp hcolors)

/-- If no actual boundary-graph edge is incident at `v`, the four actual unit
cells around that vertex have equal membership in the selected finite set. -/
theorem latticeCellBoundaryGraph_isolated_vertex_four_cells_agree
    (F : Finset LatticeVertex) (v : LatticeVertex)
    (hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj v w) :
    ((v ∈ F) ↔ ((v.1 - 1, v.2) ∈ F)) ∧
    ((v ∈ F) ↔ ((v.1, v.2 - 1) ∈ F)) ∧
    (((v.1 - 1, v.2) ∈ F) ↔ ((v.1 - 1, v.2 - 1) ∈ F)) ∧
    (((v.1, v.2 - 1) ∈ F) ↔ ((v.1 - 1, v.2 - 1) ∈ F)) := by
  let eRight : LatticeBond := ⟨v, LatticeAxis.horizontal⟩
  let eUp : LatticeBond := ⟨v, LatticeAxis.vertical⟩
  let eLeft : LatticeBond := ⟨(v.1 - 1, v.2), LatticeAxis.horizontal⟩
  let eDown : LatticeBond := ⟨(v.1, v.2 - 1), LatticeAxis.vertical⟩
  have hRight : eRight ∉ latticeCellBoundaryBonds F :=
    no_incident_boundary_bond F v hNo eRight (Or.inl rfl)
  have hUp : eUp ∉ latticeCellBoundaryBonds F :=
    no_incident_boundary_bond F v hNo eUp (Or.inl rfl)
  have hLeft : eLeft ∉ latticeCellBoundaryBonds F := by
    apply no_incident_boundary_bond F v hNo eLeft
    right
    simp [eLeft, LatticeBond.target]
  have hDown : eDown ∉ latticeCellBoundaryBonds F := by
    apply no_incident_boundary_bond F v hNo eDown
    right
    simp [eDown, LatticeBond.target]
  have hRightFaces := no_boundary_bond_implies_face_membership_agreement F eRight hRight
  have hUpFaces := no_boundary_bond_implies_face_membership_agreement F eUp hUp
  have hLeftFaces := no_boundary_bond_implies_face_membership_agreement F eLeft hLeft
  have hDownFaces := no_boundary_bond_implies_face_membership_agreement F eDown hDown
  simp only [eRight, eUp, eLeft, eDown, LatticeBond.faceBase] at hRightFaces hUpFaces hLeftFaces hDownFaces
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hUpFaces
  · simpa using hRightFaces
  · simpa using hLeftFaces
  · simpa using hDownFaces

/-- A vertex off the cycle support has no incident edge in the actual polygon
cell-boundary graph, so its four neighboring cell bases agree in membership. -/
theorem latticePolygonCycle_off_support_four_cells_agree
    {v : LatticeVertex} {p : squareLattice.Walk v v} (hp : p.IsCycle)
    (δ : PositiveMesh) (x : LatticeVertex) (hx : x ∉ p.support) :
    ((x ∈ (latticePolygonOfCycle hp).interiorCellBases δ) ↔
      ((x.1 - 1, x.2) ∈ (latticePolygonOfCycle hp).interiorCellBases δ)) ∧
    ((x ∈ (latticePolygonOfCycle hp).interiorCellBases δ) ↔
      ((x.1, x.2 - 1) ∈ (latticePolygonOfCycle hp).interiorCellBases δ)) ∧
    ((((x.1 - 1, x.2) ∈ (latticePolygonOfCycle hp).interiorCellBases δ)) ↔
      ((x.1 - 1, x.2 - 1) ∈ (latticePolygonOfCycle hp).interiorCellBases δ)) ∧
    ((((x.1, x.2 - 1) ∈ (latticePolygonOfCycle hp).interiorCellBases δ)) ↔
      ((x.1 - 1, x.2 - 1) ∈ (latticePolygonOfCycle hp).interiorCellBases δ)) := by
  classical
  let F := (latticePolygonOfCycle hp).interiorCellBases δ
  have hcycle : latticeCellBoundaryGraph F = p.toSubgraph.spanningCoe := by
    simpa [F] using latticeCellBoundaryGraph_interiorCellBases_eq_cycle hp δ
  have hNo : ∀ w, ¬ (latticeCellBoundaryGraph F).Adj x w := by
    intro w hadj
    have hedge : s(x,w) ∈ (latticeCellBoundaryGraph F).edgeSet :=
      (latticeCellBoundaryGraph F).mem_edgeSet.mpr hadj
    rw [hcycle] at hedge
    have hpEdge : s(x,w) ∈ p.edges := by
      have hiff : s(x,w) ∈ (p.toSubgraph.spanningCoe).edgeSet ↔ s(x,w) ∈ p.edges := by
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.mem_edgeSet]
      exact hiff.mp hedge
    exact hx (p.fst_mem_support_of_mem_edges hpEdge)
  simpa [F] using latticeCellBoundaryGraph_isolated_vertex_four_cells_agree F x hNo

end PottsContinuity.FKC.Domains
