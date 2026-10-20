module

public import PottsContinuity.PlanarTopology.HalfPlaneLocalUniqueness
public import PottsContinuity.PlanarTopology.LocalUniquenessProbability
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
noncomputable section

/-- Translate any finite local witness strictly into the half-plane. Its exact
probability bounds the marked half-plane uniqueness probability from below. -/
theorem halfPlaneLocalUniquenessEvent_ge_finite_witness
    (μ : Measure LatticeConfiguration) (a : LatticeVertex)
    (hμ : μ.map (latticeConfigurationTranslate a) = μ)
    (S T : Finset LatticeVertex) (hT : ∀ z ∈ T.image (latticeTranslate a), 0 < z.1) :
    μ (finiteLocalUniquenessEvent S T) ≤
      μ (halfPlaneLocalUniquenessEvent (S.image (latticeTranslate a) : Set LatticeVertex)) := by
  have hsub : finiteLocalUniquenessEvent S T ⊆
      latticeConfigurationTranslate a ⁻¹'
        halfPlaneLocalUniquenessEvent (S.image (latticeTranslate a) : Set LatticeVertex) := by
    intro ω hω
    exact finite_local_unique_subset_halfplane _ _ hT (finiteLocalUniquenessEvent_translate a S T ω hω)
  have hh := measure_mono (μ := μ) hsub
  rw [← Measure.map_apply (latticeConfigurationTranslate_measurable a)
    (halfPlaneLocalUniquenessEvent_measurableSet _),hμ] at hh
  exact hh

/-- DRT's half-plane local uniqueness limit for a fixed finite marked set
moving arbitrarily high or low and whose horizontal distance to the boundary
tends to infinity. Only translation invariance and a.s. uniqueness are used. -/
theorem halfPlaneLocalUniquenessEvent_probability_tendsto_one
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (latticeConfigurationTranslate a) = μ)
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (S : Finset LatticeVertex) (m t : ℕ → ℤ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : ℕ => μ (halfPlaneLocalUniquenessEvent
      (S.image (latticeTranslate (m n,t n)) : Set LatticeVertex))) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hbase := local_uniqueness_probability_tendsto_one μ hunique S
    have he := (tendsto_order.mp hbase).1 b hb
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    let T := S ∪ latticeBox (0,0) N
    have hprob : b < μ (finiteLocalUniquenessEvent S T) := hN N le_rfl
    have hcenter := (tendsto_atTop.mp hm) ((subgraphBoxRadius T : ℤ)+1)
    filter_upwards [hcenter] with n hn
    apply hprob.trans_le
    apply halfPlaneLocalUniquenessEvent_ge_finite_witness μ (m n,t n) (htranslation _) S T
    rintro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    have hh := (mem_latticeBox (0,0) w (subgraphBoxRadius T)).mp (subgraph_subset_boxRadius T hw)
    simp only [zero_sub,zero_add] at hh
    change 0 < w.1+m n
    omega
  · intro b hb
    exact Filter.Eventually.of_forall (fun n => lt_of_le_of_lt prob_le_one hb)

end
end PottsContinuity.PlanarTopology
