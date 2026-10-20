module

public import PottsContinuity.Thm3.RSW.TiltedStripReducedCarrier
public import PottsContinuity.PD.FK.Marginal
public import PottsContinuity.Thm3.RSW.PrewiredSubgraphMarginal
public import PottsContinuity.Thm3.RSW.StripPrunedFiniteDuality

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Thm3.Prop4
noncomputable section
local instance tiltedTopEdgeEq (N M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).edgeSet :=
  Classical.decEq _
local instance tiltedTopEdgeFintype (N M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).edgeSet :=
  Fintype.ofFinite _

/-- Exactly the original finite bonds with both endpoints in the intrinsic top class. -/
def tiltedWindowTopTopEdges (N M : ℕ) (t : ℝ) :
    Configuration (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))) := by
  classical
  exact Finset.univ.filter (fun e => ∀ z ∈ e.val, tiltedTop N t z.val)

/-- Intrinsic top-top bonds have already identified endpoints under every
boundary condition dominating the top-wired partition. -/
theorem tiltedWindowTopTopEdges_related (N M : ℕ) (t : ℝ)
    (ξ : BoundaryCondition (tiltedWindow N M t : Set (ℤ × ℤ)))
    (hξ : (tiltedWindowBoundary N M t 0).partition ≤ ξ.partition)
    (u v : (tiltedWindow N M t : Set (ℤ × ℤ)))
    (huv : (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).Adj u v)
    (he : (⟨s(u,v),(squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).mem_edgeSet.mpr huv⟩ :
      (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).edgeSet) ∈
      tiltedWindowTopTopEdges N M t) : ξ.partition.r u v := by
  classical
  simp only [tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he
  apply hξ
  exact Or.inr ⟨Or.inl (he u (by simp)),Or.inl (he v (by simp))⟩

/-- Native finite strip graph with exactly its intrinsic top-top bonds deleted. -/
def tiltedWindowReducedGraph (N M : ℕ) (t : ℝ) :=
  edgeRestriction (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))
    (tiltedWindowTopTopEdges N M t)

/-- Forgetting the independent top-top bonds gives exactly the finite FK law
on the reduced original graph, with the same top boundary partition. -/
theorem tiltedWindowReducedGraph_law (N M : ℕ) (t : ℝ)
    (θ : Parameters) (ξ : BoundaryCondition (tiltedWindow N M t : Set (ℤ × ℤ)))
    (hξ : (tiltedWindowBoundary N M t 0).partition ≤ ξ.partition) :
    (law (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))) θ ξ).map
      (subgraphConfigurationRestriction
        (edgeRestriction_le _ (tiltedWindowTopTopEdges N M t))) =
      law (tiltedWindowReducedGraph N M t) θ ξ := by
  apply law_map_subgraphRestriction_of_prewired
  intro u v huv he
  rw [subgraphRemovedEdges_edgeRestriction] at he
  exact tiltedWindowTopTopEdges_related N M t ξ hξ u v huv he

end
end PottsContinuity.RSW
