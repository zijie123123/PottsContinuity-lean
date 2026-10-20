module

public import PottsContinuity.Thm3.RSW.TiltedReducedHost

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt Thm3.Prop4
noncomputable section

/-- Genuine complementary dual configurations on the exact retained finite
source graph, embedded in its rectangular host. -/
def tiltedReducedFiniteDualEquiv (N M : ℕ) (t : ℝ) :
    Configuration (tiltedWindowReducedGraph N M t) ≃
      Configuration (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)) :=
  (isolatedExtensionConfigurationEquiv _ (tiltedReducedHostEmbedding N M t)).trans
    (rectangleSubgraphDualConfigurationEquiv (tiltedReducedHost_map_le N M t))

/-- Restrict only the independent top-top bonds, then read the actual duals
of every remaining original finite-window bond. -/
def tiltedWindowReducedDualConfiguration (N M : ℕ) (t : ℝ)
    (C : Configuration (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))) :=
  tiltedReducedFiniteDualEquiv N M t
    (subgraphConfigurationRestriction
      (edgeRestriction_le _ (tiltedWindowTopTopEdges N M t)) C)

/-- Exact finite dual law of the native tilted window after discarding
precisely its prewired top-top bonds. The actual host removed state realizes
the source boundary, so no component or partition premise remains. -/
theorem tiltedWindowReducedDualConfiguration_law (N M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (θ : Parameters) :
    (law (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))) θ
      (tiltedWindowBoundary N M t 0)).map (tiltedWindowReducedDualConfiguration N M t) =
      law (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)) (dualParameters θ)
        (embeddedSubgraphInducedDualBoundary (tiltedReducedHostEmbedding N M t)
          (tiltedReducedHost_map_le N M t) (tiltedReducedHostRemovedState N M t ht)) := by
  have hsource := positive_embedded_subgraph_induced_duality_law_PD_of_sourcePartition
    (tiltedReducedHostEmbedding N M t) (tiltedReducedHost_map_le N M t) θ
    (tiltedWindowBoundary N M t 0) (tiltedReducedHostRemovedState N M t ht)
    (tiltedReducedHost_source_partition N M t ht)
  change (law _ θ _).map (tiltedReducedFiniteDualEquiv N M t ∘
    subgraphConfigurationRestriction (edgeRestriction_le _ (tiltedWindowTopTopEdges N M t))) = _
  rw [← PMF.map_comp]
  have hremoved := tiltedWindowReducedGraph_law N M t θ (tiltedWindowBoundary N M t 0) le_rfl
  have hmap := congrArg (fun p : PMF (Configuration (tiltedWindowReducedGraph N M t)) =>
    p.map (tiltedReducedFiniteDualEquiv N M t)) hremoved
  exact hmap.trans hsource

/-- Exact self-dual-parameter specialization, for every real cluster weight
at least one and every admissible slope. -/
theorem selfDual_tiltedWindowReducedDualConfiguration_law
    (q : Set.Ici (1 : ℝ)) (N M : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (law (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))) (selfDualParameters q)
      (tiltedWindowBoundary N M t 0)).map (tiltedWindowReducedDualConfiguration N M t) =
      law (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)) (selfDualParameters q)
        (embeddedSubgraphInducedDualBoundary (tiltedReducedHostEmbedding N M t)
          (tiltedReducedHost_map_le N M t) (tiltedReducedHostRemovedState N M t ht)) := by
  simpa only [selfDualParameters_fixed] using
    tiltedWindowReducedDualConfiguration_law N M t ht (selfDualParameters q)

end
end PottsContinuity.RSW
