-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonCellFillingBoundary.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygonCellBoundaryCriterion

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open PottsContinuity.FKC.Medial

noncomputable section

/-- Equal actual interior-cell carriers determine the same normalized polygon
boundary bonds. This is a statement about the unoriented boundary-bond set;
it does not identify an ordering of polygon vertices. -/
theorem boundaryBondSet_eq_of_interiorCellBases_eq
    {m n : ℕ} (P : LatticePolygon m) (Q : LatticePolygon n)
    (δ : PositiveMesh)
    (hfill : P.interiorCellBases δ = Q.interiorCellBases δ)
    (e : LatticeBond) :
    (∃ i : ZMod (m + 3), e = P.boundaryBond i) ↔
      (∃ j : ZMod (n + 3), e = Q.boundaryBond j) := by
  have hstatus (c : LatticeVertex) :
      (latticeCellCenter δ c ∈ P.domain δ) ↔
        (latticeCellCenter δ c ∈ Q.domain δ) := by
    rw [← P.mem_interiorCellBases_iff δ c, hfill,
      Q.mem_interiorCellBases_iff δ c]
  constructor
  · intro hPboundary
    have hPdiff := (P.cellCenters_differ_iff_boundaryBond δ e).2 hPboundary
    have hQdiff :
        (latticeCellCenter δ (e.faceBase true) ∈ Q.domain δ) ≠
          (latticeCellCenter δ (e.faceBase false) ∈ Q.domain δ) := by
      intro hsame
      apply hPdiff
      calc
        (latticeCellCenter δ (e.faceBase true) ∈ P.domain δ) =
            (latticeCellCenter δ (e.faceBase true) ∈ Q.domain δ) :=
          propext (hstatus (e.faceBase true))
        _ = (latticeCellCenter δ (e.faceBase false) ∈ Q.domain δ) := hsame
        _ = (latticeCellCenter δ (e.faceBase false) ∈ P.domain δ) :=
          (propext (hstatus (e.faceBase false))).symm
    exact (Q.cellCenters_differ_iff_boundaryBond δ e).1 hQdiff
  · intro hQboundary
    have hQdiff := (Q.cellCenters_differ_iff_boundaryBond δ e).2 hQboundary
    have hPdiff :
        (latticeCellCenter δ (e.faceBase true) ∈ P.domain δ) ≠
          (latticeCellCenter δ (e.faceBase false) ∈ P.domain δ) := by
      intro hsame
      apply hQdiff
      calc
        (latticeCellCenter δ (e.faceBase true) ∈ Q.domain δ) =
            (latticeCellCenter δ (e.faceBase true) ∈ P.domain δ) :=
          (propext (hstatus (e.faceBase true))).symm
        _ = (latticeCellCenter δ (e.faceBase false) ∈ P.domain δ) := hsame
        _ = (latticeCellCenter δ (e.faceBase false) ∈ Q.domain δ) :=
          propext (hstatus (e.faceBase false))
    exact (P.cellCenters_differ_iff_boundaryBond δ e).1 hPdiff

end
end PottsContinuity.FKC.LatticePolygon
