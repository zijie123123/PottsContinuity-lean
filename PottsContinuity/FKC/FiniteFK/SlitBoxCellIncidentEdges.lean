-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCellIncidentEdges.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateBaseEdges
public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryGraph
public import PottsContinuity.FKC.Domains.LatticeCellBoundary
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open PottsContinuity.FKC.LatticePolygon

/-- Slit-graph edges whose primal bonds touch at least one cell in `F`. -/
noncomputable def slitBoxCellIncidentEdges (n : ℕ) (F : Finset LatticeVertex) :
    Finset (slitBoxGraph n).edgeSet := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ b : LatticeBond,
      b.toSym2 = Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val ∧
        (b.faceBase true ∈ F ∨ b.faceBase false ∈ F)

theorem mem_slitBoxCellIncidentEdges (n : ℕ) (F : Finset LatticeVertex)
    (e : (slitBoxGraph n).edgeSet) :
    e ∈ slitBoxCellIncidentEdges n F ↔
      ∃ b : LatticeBond,
        b.toSym2 = Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val ∧
          (b.faceBase true ∈ F ∨ b.faceBase false ∈ F) := by
  classical
  simp [slitBoxCellIncidentEdges]

private theorem candidate_path_edge_incident_to_actual_cells
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (F : Finset LatticeVertex)
    (hfill : (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ⊆ F)
    (e : Sym2 (SlitBoxVertex n))
    (he : e ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges) :
    ∃ b : LatticeBond,
      b.toSym2 = Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e ∧
        (b.faceBase true ∈ F ∨ b.faceBase false ∈ F) := by
  let cycle := slitBoxFirstHitCandidateCycle n hn u huY huX p
  let P := slitBoxFirstHitCandidatePolygon n hn u huY huX p
  have hcycle : cycle.IsCycle := slitBoxFirstHitCandidateCycle_isCycle n hn u huY huX p
  have heGraph : e ∈ (slitBoxGraph n).edgeSet :=
    (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges_subset_edgeSet he
  let eGraph : (slitBoxGraph n).edgeSet := ⟨e, heGraph⟩
  have heCycle : Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e ∈ cycle.edges := by
    exact (slitBoxFirstHitCandidateCycle_slitEdge_mem_iff n hn u huY huX p eGraph).2
      (by simpa [eGraph] using he)
  obtain ⟨i, hi⟩ := (latticePolygonOfCycle_edge_iff hcycle _).mp heCycle
  let b : LatticeBond := P.boundaryBond i
  have hbSym2 : b.toSym2 = Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e := by
    change (P.boundaryBond i).toSym2 = _
    rw [P.boundaryBond_toSym2]
    simpa [P, slitBoxFirstHitCandidatePolygon, cycle,
      slitBoxFirstHitCandidateCycle] using hi.symm
  have hbBoundary : b ∈ latticeCellBoundaryBonds (P.interiorCellBases δ) := by
    apply (mem_latticeCellBoundaryBonds_interiorCellBases_iff_boundaryBond P δ b).2
    exact ⟨i, by simp [b]⟩
  have hdiff := (mem_latticeCellBoundaryBonds _ _).mp hbBoundary
  by_cases ht : b.faceBase true ∈ P.interiorCellBases δ
  · exact ⟨b, hbSym2, Or.inl (hfill ht)⟩
  · have hf : b.faceBase false ∈ P.interiorCellBases δ := by
      by_contra hnot
      exact hdiff (by simp [ht, hnot])
    exact ⟨b, hbSym2, Or.inr (hfill hf)⟩

/-- A candidate's original path edges are incident to every cell set containing
its actual polygon filling. -/
theorem slitBoxCandidatePathEdges_subset_cellIncidentEdges_of_filling_subset
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (p : SlitBoxFirstHitBaseCandidates n u)
    (F : Finset LatticeVertex)
    (hfill : (slitBoxFirstHitCandidatePolygon n hn u huY huX p).interiorCellBases δ ⊆ F) :
    ∀ e : (slitBoxGraph n).edgeSet,
      e.val ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges →
      e ∈ slitBoxCellIncidentEdges n F := by
  intro e he
  exact (mem_slitBoxCellIncidentEdges n F e).2 <|
    candidate_path_edge_incident_to_actual_cells n hn u huY huX δ p F hfill e.val he

end PottsContinuity.FKC.FiniteFK
