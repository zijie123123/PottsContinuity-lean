module

public import PottsContinuity.PD.RCInfinite.SpatialComparison
public import PottsContinuity.PD.RCInfinite.LimitComparison
public import PottsContinuity.PD.Defs.IsRCInfiniteVolumeLimit
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Order.CompletePartialOrder

/-! Local event comparison for free and wired square-box FK laws. -/

@[expose] public section

open MeasureTheory Filter Set Topology

namespace PottsContinuity.Infinite

open PottsContinuity.PD.FK
open PottsContinuity.PD
open PottsContinuity.PD.RCInfinite

noncomputable section

private theorem boxExtension_mono (i : Fin 2) (c : LatticeVertex) (r : ℕ) :
    Monotone (boxExtension i c r) := by
  intro C D hCD e
  by_cases he : e ∈ boxEdges c r
  · obtain ⟨f, hf⟩ := he
    rw [← hf, boxExtension_at, boxExtension_at]
    by_cases hC : f ∈ C
    · have hD := hCD hC
      simp [hC, hD]
    · simp [hC]
  · fin_cases i
    · simp [boxExtension, boxConfiguration_outside c r C e he,
        boxConfiguration_outside c r D e he]
    · simp [boxExtension, wiredBoxConfiguration_outside c r C e he,
        wiredBoxConfiguration_outside c r D e he]

private theorem boxExtension_preimage_upper
    (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    {A : Set LatticeConfiguration} (hA : IsUpperSet A) :
    IsUpperSet ((boxExtension i c r) ⁻¹' A) := by
  intro C D hCD hC
  exact hA (boxExtension_mono i c r hCD) hC

private theorem boxExtension_preimage_eq_of_dependsOn
    (c : LatticeVertex) (r : ℕ) {A : Set LatticeConfiguration}
    (hA : DependsOn (boxEdges c r) A) :
    (boxExtension 0 c r) ⁻¹' A = (boxExtension 1 c r) ⁻¹' A := by
  ext C
  apply hA
  intro e he
  obtain ⟨f, hf⟩ := he
  rw [← hf, boxExtension_at, boxExtension_at]

private theorem boxEdges_subset_of_latticeBox_subset
    {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s) : boxEdges c r ⊆ boxEdges d s := by
  intro e he
  obtain ⟨f, hf⟩ := he
  refine ⟨embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
    (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) f, ?_⟩
  calc
    boxEdgeEmbedding d s
        (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
          (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) f) =
      boxEdgeEmbedding c r f := boxEdgeEmbedding_compatible hbox f
    _ = e := hf

/-- On a local increasing event, the finite free law is stochastically below
the finite wired law on the same box. -/
theorem finite_free_le_wired_local
    (θ : Parameters) (c : LatticeVertex) (r : ℕ)
    {A : Set LatticeConfiguration} (hA : IsCylinder A)
    (hdep : DependsOn (boxEdges c r) A) (hupper : IsUpperSet A) :
    ENNReal.toReal ((boxProbabilityMeasure θ c r : Measure LatticeConfiguration) A) ≤
      ENNReal.toReal ((wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) A) := by
  have hfree := boxMeasure_apply θ 0 c r hA.measurableSet
  have hwired := boxMeasure_apply θ 1 c r hA.measurableSet
  change ENNReal.toReal ((boxMeasure θ 0 c r : Measure LatticeConfiguration) A) ≤
    ENNReal.toReal ((boxMeasure θ 1 c r : Measure LatticeConfiguration) A)
  rw [hfree, hwired]
  rw [← boxExtension_preimage_eq_of_dependsOn c r hdep]
  have hpart : (boxBoundary 0 c r).partition ≤ (boxBoundary 1 c r).partition := by
    change (BoundaryCondition.free (∅ : Set (BoxVertex c r))).partition ≤
      (BoundaryCondition.wired (boxVertexBoundary c r)).partition
    change (⊥ : Setoid (BoxVertex c r)) ≤ _
    exact bot_le
  exact measure_boundary_comparison θ (boxBoundary 0 c r) (boxBoundary 1 c r)
    hpart ((boxExtension 0 c r) ⁻¹' A) (boxExtension_preimage_upper 0 c r hupper)

/-- A local increasing event under a wired infinite-volume limit is bounded
above by its probability under every wired box law containing its support. -/
theorem limit_le_wired_box_local
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m : ℕ) {A : Set LatticeConfiguration} (hA : IsCylinder A)
    (hdep : DependsOn (boxEdges (0, 0) m) A) (hupper : IsUpperSet A) :
    μ.real A ≤ (boxMeasure θ 1 (0, 0) m : Measure LatticeConfiguration).real A := by
  have hfixed (n : ℕ) (hmn : m ≤ n) :
      (boxMeasure θ 1 (0, 0) n : Measure LatticeConfiguration).real A ≤
        (boxMeasure θ 1 (0, 0) m : Measure LatticeConfiguration).real A := by
    have hbox := latticeBox_mono (0, 0) hmn
    have hout : DependsOn (boxEdges (0, 0) m)ᶜ Set.univ := by
      intro ω η _
      simp
    have hpart : ∀ K : RemovedConfiguration (boxGraph (0, 0) n)
        (boxRemovedEdges hbox),
        (isolatedExtensionPullbackBoundary (boxVertexEmbedding hbox)
          (frozenBoundary (boxBoundary 1 (0, 0) n) K.val)).partition ≤
            (boxBoundary 1 (0, 0) m).partition := by
      intro K
      simpa [boxBoundary] using
        isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
          (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox)
          (boxVertexBoundary (0, 0) m)
          (fun _ hx _ hxy => boxInterior_neighbor_closed hbox hx hxy)
          (BoundaryCondition.wired (boxVertexBoundary (0, 0) n))
          (fun _ hx => boxInterior_avoids_outerBoundary hbox hx) K
    have hjoint := box_joint_le_of_partitions θ 1 hbox A Set.univ
      hA.measurableSet MeasurableSet.univ hdep hout
      (boxExtension_preimage_upper 1 (0, 0) m hupper) hpart
    simpa [boxMeasure_wired, Measure.real] using hjoint
  have hconv := tendsto_cylinder_probability θ 1 μ hμ hA
  apply le_of_tendsto_of_tendsto hconv tendsto_const_nhds
  filter_upwards [eventually_ge_atTop m] with n hn
  exact hfixed n hn

/-- Local increasing events satisfy free-to-wired stochastic domination in
infinite volume. -/
theorem free_limit_le_wired_limit_local
    (θ : Parameters) (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ₁)
    (m : ℕ) {A : Set LatticeConfiguration} (hA : IsCylinder A)
    (hdep : DependsOn (boxEdges (0, 0) m) A) (hupper : IsUpperSet A) :
    μ₀.real A ≤ μ₁.real A := by
  have hfree := tendsto_cylinder_probability θ 0 μ₀ hμ₀ hA
  have hwired := tendsto_cylinder_probability θ 1 μ₁ hμ₁ hA
  apply le_of_tendsto_of_tendsto hfree hwired
  filter_upwards [eventually_ge_atTop m] with n hn
  have hbox := latticeBox_mono (0, 0) hn
  have hdepN : DependsOn (boxEdges (0, 0) n) A := by
    exact PottsContinuity.PD.RCInfinite.DependsOn.mono hdep
      (boxEdges_subset_of_latticeBox_subset hbox)
  have hfinite := finite_free_le_wired_local θ (0, 0) n hA hdepN hupper
  simpa only [boxMeasure_free, boxMeasure_wired, Measure.real] using hfinite

private theorem wiredBox_partition_comparison
    {m n : ℕ} (hmn : m ≤ n) :
    ∀ K : RemovedConfiguration (boxGraph (0, 0) n)
      (boxRemovedEdges (latticeBox_mono (0, 0) hmn)),
      (isolatedExtensionPullbackBoundary
        (boxVertexEmbedding (latticeBox_mono (0, 0) hmn))
        (frozenBoundary (boxBoundary 1 (0, 0) n) K.val)).partition ≤
          (boxBoundary 1 (0, 0) m).partition := by
  intro K
  simpa [boxBoundary] using
    isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
      (boxVertexEmbedding (latticeBox_mono (0, 0) hmn))
      (boxGraph_map_boxVertexEmbedding (latticeBox_mono (0, 0) hmn))
      (boxVertexBoundary (0, 0) m)
      (fun _ hx _ hxy => boxInterior_neighbor_closed (latticeBox_mono (0, 0) hmn) hx hxy)
      (BoundaryCondition.wired (boxVertexBoundary (0, 0) n))
      (fun _ hx => boxInterior_avoids_outerBoundary
        (latticeBox_mono (0, 0) hmn) hx) K

/-- Infinite-volume DMP comparison in the wired case. For every exterior
cylinder event, intersecting it with a local increasing event costs at most
the wired finite-box probability times the exterior probability. -/
theorem wired_limit_joint_le_local
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m : ℕ) {A B : Set LatticeConfiguration}
    (hA : IsCylinder A) (hB : IsCylinder B)
    (hin : DependsOn (boxEdges (0, 0) m) A)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B)
    (hupper : IsUpperSet A) :
    μ.real (A ∩ B) ≤
      (boxMeasure θ 1 (0, 0) m : Measure LatticeConfiguration).real A * μ.real B := by
  have hAB : IsCylinder (A ∩ B) := hA.inter hB
  have hleft := tendsto_cylinder_probability θ 1 μ hμ hAB
  have hconst : Tendsto
      (fun _ : ℕ => (boxMeasure θ 1 (0, 0) m : Measure LatticeConfiguration).real A)
      atTop (𝓝 ((boxMeasure θ 1 (0, 0) m : Measure LatticeConfiguration).real A)) :=
    tendsto_const_nhds
  have hright := hconst.mul (tendsto_cylinder_probability θ 1 μ hμ hB)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop m] with n hn
  have hbox := latticeBox_mono (0, 0) hn
  have hjoint := box_joint_le_of_partitions θ 1 hbox A B
    hA.measurableSet hB.measurableSet hin hout
    (boxExtension_preimage_upper 1 (0, 0) m hupper)
    (wiredBox_partition_comparison hn)
  simpa only [boxMeasure_wired, Measure.real] using hjoint

end
end PottsContinuity.Infinite
