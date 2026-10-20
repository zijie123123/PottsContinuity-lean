-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleDualLeftHalfEmbedding.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleDualRightBoundaryPath
public import PottsContinuity.FKC.FiniteFK.ReachabilityLabels
public import PottsContinuity.FKC.FiniteFK.RectangleDualConfiguration
public import PottsContinuity.FKC.FiniteFK.RectangleLabelCutIncidence
public import PottsContinuity.FKC.FiniteFK.RectangleCrossingIntersection
public import PottsContinuity.FKC.Curves.RectanglePathIntersection
public import PottsContinuity.FKC.Curves.LatticeWalkInterpolation

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

/-- The left half rectangle `[-N,0] × [0,2n]` is an actual induced
subrectangle of `[-N,N] × [0,2n]`. -/
theorem rectangleLeftHalf_subset_full (N n : ℕ) :
    latticeRectangle (-(N : ℤ), 0) N (2*n) ⊆
      latticeRectangle (-(N : ℤ), 0) (2*N) (2*n) := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  rcases hv with ⟨⟨hxl,hxr⟩,⟨hyl,hyr⟩⟩
  exact ⟨⟨by omega, by omega⟩, ⟨hyl,hyr⟩⟩

def rectangleLeftHalfVertexEmbedding (N n : ℕ) :
    RectangleVertex (-(N : ℤ), 0) N (2*n) ↪
      RectangleVertex (-(N : ℤ), 0) (2*N) (2*n) :=
  rectangleVertexEmbedding (rectangleLeftHalf_subset_full N n)

@[simp] theorem rectangleLeftHalfVertexEmbedding_val (N n : ℕ)
    (v : RectangleVertex (-(N : ℤ), 0) N (2*n)) :
    (rectangleLeftHalfVertexEmbedding N n v).val = v.val := rfl

 theorem rectangleLeftHalfDual_subset_full (N n : ℕ) :
    rectangleDualExpanded (-(N : ℤ), 0) N (2*n) ⊆
      rectangleDualExpanded (-(N : ℤ), 0) (2*N) (2*n) := by
  intro z hz
  rw [rectangleDualExpanded, mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hxl,hxr⟩,⟨hyl,hyr⟩⟩
  exact ⟨⟨hxl,by omega⟩,⟨hyl,hyr⟩⟩

/-- Same-coordinate embedding of expanded dual face vertices. -/
def rectangleLeftHalfDualVertexEmbedding (N n : ℕ) :
    RectangleDualVertex (-(N : ℤ), 0) N (2*n) ↪
      RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n) where
  toFun z := ⟨z.val, rectangleLeftHalfDual_subset_full N n z.property⟩
  inj' := by
    intro x y h
    have hval : x.val = y.val := by
      simpa only using congrArg
        (fun z : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n) => z.val) h
    apply Subtype.ext
    exact hval

@[simp] theorem rectangleLeftHalfDualVertexEmbedding_val (N n : ℕ)
    (z : RectangleDualVertex (-(N : ℤ), 0) N (2*n)) :
    (rectangleLeftHalfDualVertexEmbedding N n z).val = z.val := rfl

/-- Labels in the half rectangle are restrictions of actual full-rectangle
reachability labels, with all paths allowed to use the full rectangle. -/
def rectangleLeftHalfReachabilityLabel (N n : ℕ)
    (A : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    (L : Finset (RectangleVertex (-(N : ℤ), 0) (2*N) (2*n))) :
    RectangleVertex (-(N : ℤ), 0) N (2*n) → Bool :=
  fun v => actualReachabilityLabel
    (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L
    (rectangleLeftHalfVertexEmbedding N n v)

/-- A label-cut dual edge in the half rectangle is an actual open edge of the
full complementary dual configuration. -/
theorem rectangleLeftHalf_labelCut_adj_is_fullDual_open
    (N n : ℕ)
    (A : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    (L : Finset (RectangleVertex (-(N : ℤ), 0) (2*N) (2*n)))
    (u v : RectangleDualVertex (-(N : ℤ), 0) N (2*n))
    (hadj : (rectangleLabelCutDualGraph (-(N : ℤ), 0) N (2*n)
      (rectangleLeftHalfReachabilityLabel N n A L)).Adj u v) :
    (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
      (rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) A)).Adj
      (rectangleLeftHalfDualVertexEmbedding N n u)
      (rectangleLeftHalfDualVertexEmbedding N n v) := by
  obtain ⟨b, hs, ht, hdiff, hfaces⟩ :=
    (rectangleLabelCutDual_adj_iff_bond (-(N : ℤ), 0) N (2*n)
      (rectangleLeftHalfReachabilityLabel N n A L) u v).mp hadj
  let hu : RectangleVertex (-(N : ℤ), 0) (2*N) (2*n) :=
    ⟨b.source, rectangleLeftHalf_subset_full N n hs⟩
  let hv : RectangleVertex (-(N : ℤ), 0) (2*N) (2*n) :=
    ⟨b.target, rectangleLeftHalf_subset_full N n ht⟩
  have hlabelS : rectangleLeftHalfReachabilityLabel N n A L ⟨b.source, hs⟩ =
      actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L hu := by
    change actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L
      (rectangleLeftHalfVertexEmbedding N n ⟨b.source, hs⟩) = _
    congr 1
  have hlabelT : rectangleLeftHalfReachabilityLabel N n A L ⟨b.target, ht⟩ =
      actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L hv := by
    change actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L
      (rectangleLeftHalfVertexEmbedding N n ⟨b.target, ht⟩) = _
    congr 1
  have hlabels : actualReachabilityLabel
      (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L hu ≠
      actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L hv := by
    intro heq
    have hdiff' := hdiff
    rw [hlabelS, hlabelT, heq] at hdiff'
    simp at hdiff'
  let bp : RectanglePrimalBond (-(N : ℤ), 0) (2*N) (2*n) :=
    ⟨b, rectangleLeftHalf_subset_full N n hs,
      rectangleLeftHalf_subset_full N n ht⟩
  let ep := rectanglePrimalBondToEdge (-(N : ℤ), 0) (2*N) (2*n) bp
  have hbond : rectanglePrimalEdgeBond (-(N : ℤ), 0) (2*N) (2*n) ep = b := by
    have hh := (rectanglePrimalEdgeBondEquiv (-(N : ℤ), 0) (2*N) (2*n)).right_inv bp
    exact congrArg Subtype.val hh
  have hG : s(hu,hv) ∈ (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)).edgeSet := by
    exact ep.2
  have hnotA : (⟨s(hu,hv), hG⟩ :
      (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)).edgeSet) ∉ A :=
    actualEdge_not_mem_configuration_of_labels_ne
      (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L hG hlabels
  let d : RectangleDualEdgeCarrier (-(N : ℤ), 0) (2*N) (2*n) :=
    rectanglePrimalDualEdgeEquiv (-(N : ℤ), 0) (2*N) (2*n) ep
  have hdconfig : rectangleDualGraphEdgeEquiv (-(N : ℤ), 0) (2*N) (2*n) d ∈
      rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) A := by
    apply (mem_rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) A d).2
    change ep ∉ A
    exact hnotA
  have hdBond : rectanglePrimalEdgeBond (-(N : ℤ), 0) (2*N) (2*n)
      d.primalEdge = b := by
    change rectanglePrimalEdgeBond (-(N : ℤ), 0) (2*N) (2*n) ep = b
    exact hbond
  have hpair : s(rectangleLeftHalfDualVertexEmbedding N n u,
      rectangleLeftHalfDualVertexEmbedding N n v) =
      rectangleDualCarrierPair (-(N : ℤ), 0) (2*N) (2*n) d := by
    rcases hfaces with hfaces | hfaces
    · have hsource : (rectangleLeftHalfDualVertexEmbedding N n u).val =
          (rectangleDualEdgeSource (-(N : ℤ), 0) (2*N) (2*n) d).val := by
        rw [rectangleLeftHalfDualVertexEmbedding_val,
          rectangleDualEdgeSource_faceBase, hdBond]
        exact hfaces.1
      have htarget : (rectangleLeftHalfDualVertexEmbedding N n v).val =
          (rectangleDualEdgeTarget (-(N : ℤ), 0) (2*N) (2*n) d).val := by
        rw [rectangleLeftHalfDualVertexEmbedding_val,
          rectangleDualEdgeTarget_faceBase, hdBond]
        exact hfaces.2
      apply Sym2.eq_iff.mpr
      left
      exact ⟨Subtype.ext hsource, Subtype.ext htarget⟩
    · have hsource : (rectangleLeftHalfDualVertexEmbedding N n u).val =
          (rectangleDualEdgeTarget (-(N : ℤ), 0) (2*N) (2*n) d).val := by
        rw [rectangleLeftHalfDualVertexEmbedding_val,
          rectangleDualEdgeTarget_faceBase, hdBond]
        exact hfaces.1
      have htarget : (rectangleLeftHalfDualVertexEmbedding N n v).val =
          (rectangleDualEdgeSource (-(N : ℤ), 0) (2*N) (2*n) d).val := by
        rw [rectangleLeftHalfDualVertexEmbedding_val,
          rectangleDualEdgeSource_faceBase, hdBond]
        exact hfaces.2
      apply Sym2.eq_iff.mpr
      right
      exact ⟨Subtype.ext hsource, Subtype.ext htarget⟩
  rw [openGraph_adj]
  refine ⟨rectangleDualGraphEdgeEquiv (-(N : ℤ), 0) (2*N) (2*n) d,
    hdconfig, ?_⟩
  change rectangleDualCarrierPair (-(N : ℤ), 0) (2*N) (2*n) d = _
  exact hpair.symm

/-- A label-cut dual path in the half rectangle transports to a true path in
full-rectangle complementary dual-open edges. -/
theorem rectangleLeftHalf_labelCut_reachable_is_fullDual_open
    (N n : ℕ)
    (A : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    (L : Finset (RectangleVertex (-(N : ℤ), 0) (2*N) (2*n)))
    (u v : RectangleDualVertex (-(N : ℤ), 0) N (2*n))
    (hconn : (rectangleLabelCutDualGraph (-(N : ℤ), 0) N (2*n)
      (rectangleLeftHalfReachabilityLabel N n A L)).Reachable u v) :
    (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
      (rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) A)).Reachable
      (rectangleLeftHalfDualVertexEmbedding N n u)
      (rectangleLeftHalfDualVertexEmbedding N n v) := by
  rcases hconn with ⟨p⟩
  let f : SimpleGraph.Hom
      (rectangleLabelCutDualGraph (-(N : ℤ), 0) N (2*n)
        (rectangleLeftHalfReachabilityLabel N n A L))
      (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
        (rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) A)) :=
    ⟨rectangleLeftHalfDualVertexEmbedding N n,
      by
        intro x y hxy
        exact rectangleLeftHalf_labelCut_adj_is_fullDual_open N n A L x y hxy⟩
  change Nonempty ((openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
    (rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) A)).Walk (f u) (f v))
  exact ⟨p.map f⟩

end
end PottsContinuity.FKC.FiniteFK
