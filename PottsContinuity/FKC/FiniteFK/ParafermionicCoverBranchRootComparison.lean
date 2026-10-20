-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverBranchRootComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverEq24RootCoreComparison
public import PottsContinuity.FKC.FiniteFK.AdjacentBoundaryConnectionLowerBound

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance branchRootVertexFintype (n : ℕ) :
    Fintype (rectangleDualBottomCollarInnerVertex n) := Fintype.ofFinite _
local instance branchRootVertexDecidableEq (n : ℕ) :
    DecidableEq (rectangleDualBottomCollarInnerVertex n) := Classical.decEq _
local instance branchRootDualEdgeFintype (n : ℕ) :
    Fintype (rectangleDualBottomCollarInnerGraph n).edgeSet := Fintype.ofFinite _
local instance branchRootDualEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleDualBottomCollarInnerGraph n).edgeSet := Classical.decEq _
local instance branchRootDualCfgFintype (n : ℕ) :
    Fintype (Configuration (rectangleDualBottomCollarInnerGraph n)) := Fintype.ofFinite _
local instance branchRootAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance branchRootAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

 theorem branchRootVertex_mem (n : ℕ) (hn : 1 ≤ n) :
    (0,-1) ∈ rectangleDualExpanded (-(n:ℤ),0) (2*n) n := by
  change (0,-1) ∈ latticeRectangle (-(n:ℤ)-1,-1) (2*n+1) (n+1)
  rw [mem_latticeRectangle]
  constructor <;> constructor <;> omega

/-- The literal branch face base immediately below `(0,0)` in the true dual. -/
def parafermionicCoverBranchRootVertex (n : ℕ) (hn : 1 ≤ n) :
    rectangleDualBottomCollarInnerVertex n :=
  ⟨(0,-1), branchRootVertex_mem n hn⟩

/-- Actual true-dual connection from the branch face base to the full
left/right/top boundary. This is distinct from the Eq. 24 root event. -/
def parafermionicCoverBranchRootEvent (n : ℕ) (hn : 1 ≤ n) :
    Set (Configuration (rectangleDualBottomCollarInnerGraph n)) :=
  {D | ∃ z ∈ rectangleDualBottomCollarInnerThreeSides n,
    ActualConnected (rectangleDualBottomCollarInnerGraph n) D
      (parafermionicCoverBranchRootVertex n hn) z}

theorem parafermionicCoverBranchRootEvent_isUpperSet (n : ℕ) (hn : 1 ≤ n) :
    IsUpperSet (parafermionicCoverBranchRootEvent n hn) := by
  intro A B hAB hA
  rcases hA with ⟨z, hz, hconn⟩
  exact ⟨z, hz, actualConnected_mono hAB hconn⟩

private theorem parafermionicCoverBranchRoot_adj_origin (n : ℕ) (hn : 1 ≤ n) :
    (rectangleDualBottomCollarInnerGraph n).Adj
      (parafermionicCoverBranchRootVertex n hn)
      (parafermionicCoverEq24DualOriginVertex n) := by
  apply (generalRectangleDualBottomRow_adj_iff (-(n:ℤ),0) (2*n) n 0 _ _ rfl rfl).2
  constructor <;> omega

/-- A single actual dual edge from the branch face base to the origin gives a
one-factor lower bound by the ordinary rectangle's literal origin event. -/
theorem measure_parafermionicCoverBranchRootEvent_lower_bound
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight) :
    (1 / (1 + loopWeight q) : ℝ) *
      (measure (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) q
        (BoundaryCondition.wired
          (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n))
        (parafermionicCoverEq24OrdinaryOriginEvent n)).toReal ≤
      (measure (rectangleDualBottomCollarInnerGraph n) q
        (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n))
        (parafermionicCoverBranchRootEvent n hn)).toReal := by
  let T := rectangleDualBottomCollarInnerThreeSides n
  let ξ := BoundaryCondition.wired T
  have h := adjacent_boundary_connection_probability_lower_bound q ξ
    (parafermionicCoverBranchRoot_adj_origin n hn) T
  have h' : (1 / (1 + loopWeight q) : ℝ) *
      (measure (rectangleDualBottomCollarInnerGraph n) q ξ
        (parafermionicCoverEq24DualOriginEvent n)).toReal ≤
      (measure (rectangleDualBottomCollarInnerGraph n) q ξ
        (parafermionicCoverBranchRootEvent n hn)).toReal := by
    simpa [ξ, T, parafermionicCoverEq24DualOriginEvent,
      parafermionicCoverBranchRootEvent] using h
  rw [← parafermionicCoverEq24OrdinaryOriginEvent_probability_eq_dualOriginEvent n q]
    at h'
  exact h'

/-- For every actual frozen outside state and every admissible layer, the
three-side dual law is dominated by the conditional cover law for the branch
root event. No sheet-separation claim is part of this comparison. -/
theorem measure_parafermionicCoverBranchRootEvent_le_conditional
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (q : ClusterWeight)
    (K : RemovedConfiguration (ParafermionicAmbientGraph n)
      (subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n))) :
    (measure (rectangleDualBottomCollarInnerGraph n) q
      (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n))
      (parafermionicCoverBranchRootEvent n hn)).toReal ≤
    ((((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).filter
      (frozenStateEvent
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)
      (frozenStateEvent_support q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)).map
      (parafermionicCoverStripDualRestriction n k hk)).toMeasure
      (parafermionicCoverBranchRootEvent n hn)).toReal := by
  exact measure_parafermionicCoverStrip_dual_threeSides_le_conditional
    n k hk q K (parafermionicCoverBranchRootEvent n hn)
    (parafermionicCoverBranchRootEvent_isUpperSet n hn)

end
end PottsContinuity.FKC.FiniteFK
