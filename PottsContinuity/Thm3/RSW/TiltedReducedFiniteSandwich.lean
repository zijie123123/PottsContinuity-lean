module

public import PottsContinuity.Thm3.RSW.TiltedReducedLowerCorridor
public import PottsContinuity.Thm3.RSW.TiltedReducedUpperPartition
public import PottsContinuity.Thm3.RSW.EmbeddedComparison
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt Thm3.Prop4
noncomputable section

/-- Every increasing reduced-core event is squeezed between the native
top-only and top-with-sides laws, under the exact genuine finite dual law. -/
theorem tiltedReducedFiniteDual_probability_sandwich
    (N L M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hM : L+N+3 ≤ M) (θ : Parameters)
    (S : Set (Configuration (tiltedWindowReducedGraph N L t))) (hS : IsUpperSet S) :
    (measure (tiltedWindowReducedGraph N L t) θ (tiltedWindowBoundary N L t 0) S).toReal ≤
      (measure (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)) θ
        (tiltedReducedFiniteDualBoundary N M t ht)
        {C | embeddedConfigurationRestriction _ _ (tiltedReducedCoreDualEmbedding N L M t hM)
          (tiltedReducedCoreDual_map_le N L M t ht hM) C ∈ S}).toReal ∧
    (measure (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)) θ
        (tiltedReducedFiniteDualBoundary N M t ht)
        {C | embeddedConfigurationRestriction _ _ (tiltedReducedCoreDualEmbedding N L M t hM)
          (tiltedReducedCoreDual_map_le N L M t ht hM) C ∈ S}).toReal ≤
      (measure (tiltedWindowReducedGraph N L t) θ (tiltedWindowBoundary N L t 1) S).toReal := by
  let G := tiltedWindowReducedGraph N L t
  let H := rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)
  let f := tiltedReducedCoreDualEmbedding N L M t hM
  let hGH := tiltedReducedCoreDual_map_le N L M t ht hM
  let η := tiltedReducedFiniteDualBoundary N M t ht
  let ξ := tiltedReducedSupportedDualBoundary N L M hN t ht hM
  have hξlaw : law H θ ξ = law H θ η := law_eq_of_boundary_partition_eq (G := H) θ ξ η rfl
  have hmass (T : Set (Configuration H)) : measure H θ ξ T = measure H θ η T := by
    unfold PD.FK.measure
    rw [hξlaw]
  constructor
  · exact (measure_boundary_comparison θ (tiltedWindowBoundary N L t 0)
      (isolatedExtensionPullbackBoundary f η)
      (tiltedReducedCore_top_partition_le N L M hN t ht hM) S hS).trans
        (embedded_boundary_probability_le G H f hGH θ η S hS)
  · rw [← hmass]
    apply embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
      G H f hGH θ ξ (tiltedWindowBoundary N L t 1) S hS
    intro K
    apply isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
      f hGH (tiltedWindowWiredVertices N L t 1)
      (fun x hx y hxy => tiltedReducedCoreDual_closedInterior N L M t ht hM x hx y hxy) ξ
      (fun x hx => tiltedReducedSupportedDualBoundary_avoids_core N L M hN t ht hM x
        (fun htop => hx (Or.inl htop))) K

end
end PottsContinuity.RSW
