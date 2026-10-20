module

public import PottsContinuity.Thm3.Prop4.TubeCentralRetainedBonds
public import PottsContinuity.PD.FK.EdgeRestriction

/-!
# Actual retained original connector bonds indexed by central rows

The set contains exactly the still-sampled original horizontal bonds in the
specified row interval. Its cardinality is bounded by the number of rows,
using the unique normalized original bond, with no selected edge witness.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- The actual primal graph after deleting the whole fixed tube reveal,
retaining every original physical rectangle vertex. -/
abbrev tubePrimalRemainingGraph (n : ℕ) (r : ℝ) (u v : LatticeVertex) :
    SimpleGraph (RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
  edgeRestriction (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (rectangleTubeRevealedEdges n r u v)

local instance retainedRowsEdgeFintype (n : ℕ) (r : ℝ) (u v : LatticeVertex) :
    Fintype (tubePrimalRemainingGraph n r u v).edgeSet := Fintype.ofFinite _

/-- Exactly the actual unrevealed original central horizontal bonds whose
integer rows belong to the specified interval, on the genuine remaining graph. -/
def tubeRemainingCentralRows (n : ℕ) (r : ℝ) (u v : LatticeVertex) (a b : ℤ) :
    Configuration (tubePrimalRemainingGraph n r u v) := by
  classical
  exact Finset.univ.filter (fun e => ∃ y ∈ Finset.Icc a b,
    Sym2.map Subtype.val e.val = s((0,y),(1,y)))

private theorem retained_row_canonical_bond (n : ℕ) (r : ℝ) (u v : LatticeVertex) (a b : ℤ)
    (e : (tubePrimalRemainingGraph n r u v).edgeSet)
    (he : e ∈ tubeRemainingCentralRows n r u v a b) :
    ∃ y ∈ Finset.Icc a b,
      rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (edgeRestrictionEdgeEmbedding _ (rectangleTubeRevealedEdges n r u v) e) =
        ⟨(0,y),.horizontal⟩ := by
  classical
  obtain ⟨y,hy,hcoords⟩ := (Finset.mem_filter.mp he).2
  refine ⟨y,hy,?_⟩
  let eOrig := edgeRestrictionEdgeEmbedding _ (rectangleTubeRevealedEdges n r u v) e
  have hnorm := congrArg Subtype.val (wholePlaneBondEdgeEquiv.apply_symm_apply
    (rectanglePrimalEdgeToSquareEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) eOrig))
  change (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) eOrig).toSym2 =
    Sym2.map Subtype.val e.val at hnorm
  apply LatticeBond.toSym2_injective
  exact hnorm.trans hcoords

/-- Distinct retained central original bonds have distinct rows; hence no
finite-energy count is hidden by the carrier or by a missing sampled edge. -/
theorem tubeRemainingCentralRows_card_le (n : ℕ) (r : ℝ) (u v : LatticeVertex) (a b : ℤ) :
    (tubeRemainingCentralRows n r u v a b).card ≤ (Finset.Icc a b).card := by
  classical
  let row : (tubePrimalRemainingGraph n r u v).edgeSet → ℤ := fun e =>
    (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (edgeRestrictionEdgeEmbedding _ (rectangleTubeRevealedEdges n r u v) e)).base.2
  apply Finset.card_le_card_of_injOn row
  · intro e he
    obtain ⟨y,hy,hbond⟩ := retained_row_canonical_bond n r u v a b e he
    have hrow := congrArg (fun c : LatticeBond => c.base.2) hbond
    change row e = y at hrow
    exact hrow.symm ▸ hy
  · intro e he g hg hrowEq
    obtain ⟨y,hy,hbondE⟩ := retained_row_canonical_bond n r u v a b e he
    obtain ⟨z,hz,hbondG⟩ := retained_row_canonical_bond n r u v a b g hg
    have hrowE := congrArg (fun c : LatticeBond => c.base.2) hbondE
    have hrowG := congrArg (fun c : LatticeBond => c.base.2) hbondG
    change row e = y at hrowE
    change row g = z at hrowG
    have hyz : y = z := hrowE.symm.trans (hrowEq.trans hrowG)
    have hbond : rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (edgeRestrictionEdgeEmbedding _ (rectangleTubeRevealedEdges n r u v) e) =
      rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (edgeRestrictionEdgeEmbedding _ (rectangleTubeRevealedEdges n r u v) g) := by
      rw [hbondE,hbondG,hyz]
    have hOrig := (rectanglePrimalEdgeBondEquiv (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).injective
      (Subtype.ext hbond)
    exact (edgeRestrictionEdgeEmbedding _ (rectangleTubeRevealedEdges n r u v)).injective hOrig

end
end PottsContinuity.Thm3.Prop4
