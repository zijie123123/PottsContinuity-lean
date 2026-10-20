-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/RectangleBranchCrosscutObstruction.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.RectangleBranchPathIntersection
public import PottsContinuity.FKC.Curves.RectangleCrosscutDisjointness
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchRootComparison

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Curves PottsContinuity.FKC.Medial

/-- A genuine bottom-to-bottom open primal crossing from the left half to the
right half rules out an actual branch-root connection to the dual left, right,
or top boundary. -/
theorem rectangleBranchRootEvent_not_of_openBottomCrossing
    (n : ℕ) (hn : 1 ≤ n)
    (A : Finset (rectanglePrimalEdgeCarrier (-(n : ℤ), 0) (2 * n) n))
    {u v : RectangleVertex (-(n : ℤ), 0) (2 * n) n}
    (p : (openGraph (rectangleGraph (-(n : ℤ), 0) (2 * n) n)
      (rectanglePrimalCarrierConfiguration n A)).Walk u v)
    (huBottom : u.val.2 = 0) (hvBottom : v.val.2 = 0)
    (huLeft : u.val.1 ≤ 0) (hvRight : 1 ≤ v.val.1) :
    rectangleDualConfiguration (-(n : ℤ), 0) (2 * n) n A ∉
      parafermionicCoverBranchRootEvent n hn := by
  intro hbranch
  rcases hbranch with ⟨z, hz, hconn⟩
  obtain ⟨q⟩ := (actualConnected_iff_walk
    (rectangleDualBottomCollarInnerGraph n)
    (rectangleDualConfiguration (-(n : ℤ), 0) (2 * n) n A)
    (parafermionicCoverBranchRootVertex n hn) z).mp hconn
  obtain ⟨w, hwDual, hwCrosscut⟩ :=
    rectangleBranch_primal_dual_walk_intersect n hn
      (rectanglePrimalCarrierConfiguration n A) p
      huBottom hvBottom huLeft hvRight hz q
  have hdis := rectangleLowerClosureDualPath_disjoint_upperCrosscutClosure
    n A p huBottom hvBottom q
  exact (Set.disjoint_left.mp hdis) hwDual hwCrosscut

end PottsContinuity.FKC.FiniteFK
