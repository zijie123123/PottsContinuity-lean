module

public import PottsContinuity.Coincidence.PressureContinuity
public import PottsContinuity.Critical.ThresholdConstruction
public import PottsContinuity.Critical.ThresholdMonotonicity
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Infinite.MeasurableDomination
public import PottsContinuity.PD.FK.BoxLimits
public import PottsContinuity.PD.FK.FreeBoxLimit
public import Mathlib.Topology.Order.Monotone

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Coincidence

open PottsContinuity
open PottsContinuity.BD12
open PottsContinuity.Critical
open PottsContinuity.Infinite
open PottsContinuity.PD.FK

noncomputable section

def activityParameters (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (s : ℝ) : Parameters :=
  drtHomogeneousParameters q hq (drtLogActivityTemperature s)

/-- The free box limit selected from the already-proved unique weak-limit theorem. -/
def freeActivityCanonicalLimit (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (s : ℝ) : ProbabilityMeasure LatticeConfiguration :=
  Classical.choose (PottsContinuity.PD.FK.Internal.freeBoxLimit_existsUnique
    (q := activityParameters q hq s))

theorem freeActivityCanonicalLimit_tendsto
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s : ℝ) :
    Tendsto (fun n => boxProbabilityMeasure (activityParameters q hq s) (0, 0) n)
      atTop (𝓝 (freeActivityCanonicalLimit q hq s)) := by
  exact (Classical.choose_spec
    (PottsContinuity.PD.FK.Internal.freeBoxLimit_existsUnique
      (q := activityParameters q hq s))).1
    (fun _ => (0, 0)) (fun n => n)
    origin_latticeBox_nested origin_latticeBox_exhaustive

theorem freeActivityCanonicalLimit_frozen
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s : ℝ) :
    IsRCInfiniteVolumeLimit (activityParameters q hq s).toP
      (activityParameters q hq s).toQ 0
      (freeActivityCanonicalLimit q hq s).toMeasure := by
  apply PottsContinuity.Foundations.pd_interior_limit_all_exhaustions
    (activityParameters q hq s) 0
  exact PottsContinuity.PD.FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto
    (activityParameters q hq s) (freeActivityCanonicalLimit q hq s)
    (freeActivityCanonicalLimit_tendsto q hq s)

theorem wiredActivityCanonicalLimit_frozen
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s : ℝ) :
    IsRCInfiniteVolumeLimit (activityParameters q hq s).toP
      (activityParameters q hq s).toQ 1
      (wiredBoxCanonicalLimit (activityParameters q hq s)).toMeasure := by
  apply PottsContinuity.Foundations.pd_interior_limit_all_exhaustions
    (activityParameters q hq s) 1
  exact PottsContinuity.PD.FK.isRCInfiniteVolumeLimit_of_wiredBox_tendsto
    (activityParameters q hq s) (wiredBoxCanonicalLimit (activityParameters q hq s))
    (wiredBoxCanonicalLimit_tendsto (activityParameters q hq s))

def horizontalOpenEvent : Set LatticeConfiguration :=
  LatticeConfiguration.allOpen {horizontalUnitEdge}

private theorem horizontalOpenEvent_clopen : IsClopen horizontalOpenEvent :=
  LatticeConfiguration.allOpen_isClopen _

private theorem horizontalOpenEvent_upper : IsUpperSet horizontalOpenEvent := by
  intro ω η hωη hω
  change η ∈ LatticeConfiguration.allOpen {horizontalUnitEdge}
  rw [allOpen_singleton_eq_edgeOpen]
  change η horizontalUnitEdge = true
  have hω' : ω horizontalUnitEdge = true := by
    change ω ∈ LatticeConfiguration.allOpen {horizontalUnitEdge} at hω
    rw [allOpen_singleton_eq_edgeOpen] at hω
    exact hω
  have h := hωη horizontalUnitEdge
  rw [hω'] at h
  simpa using (top_le_iff.mp h)

/-- The free horizontal-edge open probability in the chosen weak box limit. -/
def freeActivityEdgeMarginal (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (s : ℝ) : ℝ :=
  (freeActivityCanonicalLimit q hq s).toMeasure.real horizontalOpenEvent

/-- The wired horizontal-edge open probability in the canonical wired box limit. -/
def wiredActivityEdgeMarginal (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (s : ℝ) : ℝ :=
  (wiredBoxCanonicalLimit (activityParameters q hq s)).toMeasure.real horizontalOpenEvent

private theorem activityParameters_edgeParameter_mono
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) {s t : ℝ} (hst : s ≤ t) :
    edgeParameter (activityParameters q hq s) ≤ edgeParameter (activityParameters q hq t) := by
  rw [activityParameters, activityParameters, drtHomogeneousParameters_edgeParameter,
    drtHomogeneousParameters_edgeParameter]
  have hβ := drtLogActivityTemperature_monotone hst
  have hexp : Real.exp (-(drtLogActivityTemperature t : ℝ)) ≤
      Real.exp (-(drtLogActivityTemperature s : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg hβ)
  exact sub_le_sub_left hexp 1

private theorem freeActivityEdgeMarginal_monotone
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) :
    Monotone (freeActivityEdgeMarginal q hq) := by
  intro s t hst
  let θ := activityParameters q hq s
  let θ' := activityParameters q hq t
  let μ := freeActivityCanonicalLimit q hq s
  let ν := freeActivityCanonicalLimit q hq t
  have hprob := freeBoxLimit_parameter_mono_of_clopen θ θ' (by rfl)
    (activityParameters_edgeParameter_mono q hq hst) μ ν
    (freeActivityCanonicalLimit_tendsto q hq s)
    (freeActivityCanonicalLimit_tendsto q hq t)
    horizontalOpenEvent horizontalOpenEvent_clopen horizontalOpenEvent_upper
  have hmeasure : μ.toMeasure horizontalOpenEvent ≤ ν.toMeasure horizontalOpenEvent := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ENNReal.coe_le_coe.mpr hprob
  have hreal : μ.toMeasure.real horizontalOpenEvent ≤ ν.toMeasure.real horizontalOpenEvent :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 hmeasure
  simpa [freeActivityEdgeMarginal, μ, ν] using hreal

theorem freeActivityEdgeMarginal_countableDiscontinuities
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) :
    {s : ℝ | ¬ ContinuousAt (freeActivityEdgeMarginal q hq) s}.Countable :=
  (freeActivityEdgeMarginal_monotone q hq).countable_not_continuousAt

theorem freeActivityEdgeMarginal_le_wired
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s : ℝ) :
    freeActivityEdgeMarginal q hq s ≤ wiredActivityEdgeMarginal q hq s := by
  let θ := activityParameters q hq s
  let μ₀ := freeActivityCanonicalLimit q hq s
  let μ₁ := wiredBoxCanonicalLimit θ
  have hdom := free_infinite_le_wired_infinite_measurable
    θ.toP θ.toQ (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property
    μ₀.toMeasure μ₁.toMeasure (freeActivityCanonicalLimit_frozen q hq s)
    (wiredActivityCanonicalLimit_frozen q hq s) horizontalOpenEvent
    horizontalOpenEvent_clopen.1.measurableSet horizontalOpenEvent_upper
  simpa [freeActivityEdgeMarginal, wiredActivityEdgeMarginal, θ, μ₀, μ₁,
    horizontalOpenEvent] using hdom

theorem wiredActivityEdgeMarginal_le_free_largerActivity
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s t : ℝ) (hst : s < t) :
    wiredActivityEdgeMarginal q hq s ≤ freeActivityEdgeMarginal q hq t := by
  let θ₁ := activityParameters q hq s
  let θ₀ := activityParameters q hq t
  let μ₁ := wiredBoxCanonicalLimit θ₁
  let μ₀ := freeActivityCanonicalLimit q hq t
  have hpressure := wired_activity_edge_probability_le_free_larger_activity
    q hq s t hst μ₁.toMeasure μ₀.toMeasure
    (wiredActivityCanonicalLimit_frozen q hq s)
    (freeActivityCanonicalLimit_frozen q hq t)
  simpa [wiredActivityEdgeMarginal, freeActivityEdgeMarginal, θ₁, θ₀, μ₁, μ₀,
    horizontalOpenEvent] using hpressure

theorem free_wired_activityEdgeMarginals_eq_of_free_continuous
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s : ℝ)
    (hcont : ContinuousAt (freeActivityEdgeMarginal q hq) s) :
    freeActivityEdgeMarginal q hq s = wiredActivityEdgeMarginal q hq s := by
  have hright : ∀ᶠ t in 𝓝[>] s,
      -(freeActivityEdgeMarginal q hq t) ≤ -(wiredActivityEdgeMarginal q hq s) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact neg_le_neg (wiredActivityEdgeMarginal_le_free_largerActivity q hq s t ht)
  have hlim : Tendsto (fun t => -(freeActivityEdgeMarginal q hq t))
      (𝓝[>] s) (𝓝 (-(freeActivityEdgeMarginal q hq s))) :=
    hcont.neg.mono_left nhdsWithin_le_nhds
  have hupper :
      -(freeActivityEdgeMarginal q hq s) ≤ -(wiredActivityEdgeMarginal q hq s) :=
    le_of_tendsto hlim hright
  have hlower := freeActivityEdgeMarginal_le_wired q hq s
  linarith

end

end PottsContinuity.Coincidence
