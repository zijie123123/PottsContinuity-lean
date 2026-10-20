module

public import PottsContinuity.Thm4.SlitPairedWitness
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedGoodConditionalBound
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedGoodEventMass
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedGoodRecord
public import PottsContinuity.FKC.FiniteFK.FiniteConditionalGoodFiberBound

@[expose] public section

/- The strict-range disintegration proof is adapted from FKconvergence, an earlier formalization
by the same author that is not publicly accessible (see `related_formalizations` in
formalization.yaml): file `FiniteFK/SlitBoxCenterPolynomialLowerBound.lean`.
Only the pointwise pair-to-center inequality is extracted. Endpoint passage
below uses actual finite probabilities, not a conditional-law assumption. -/
namespace PottsContinuity.Thm4
open PottsContinuity.FKC PottsContinuity.FKC.FiniteFK MeasureTheory
noncomputable section

local instance centerPolynomialEdgeFintype (n : ℕ) :
    Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
local instance centerPolynomialConfigFintype (n : ℕ) :
    Fintype (Configuration (slitBoxGraph n)) := Fintype.ofFinite _
local instance centerPolynomialConfigNonempty (n : ℕ) :
    Nonempty (Configuration (slitBoxGraph n)) := ⟨∅⟩
local instance centerPolynomialConfigMeasurable (n : ℕ) :
    MeasurableSpace (Configuration (slitBoxGraph n)) := ⊤
local instance centerPolynomialConfigDiscrete (n : ℕ) :
    DiscreteMeasurableSpace (Configuration (slitBoxGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Pointwise conversion of paired-good mass to bottom-center mass in the
strict range; all record fibers and conditional probabilities are genuine. -/
theorem slit_center_probability_ge_pair_strict
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (q : ClusterWeight) :
    (1 / (20 * (n : ℝ)^4)) * slitPairConnectionProbability n ⟨q, q.2.1⟩ u ≤
      slitArcConnectionProbability n ⟨q, q.2.1⟩ (slitBoxBottomCenterVertex n) := by
  let δ : PositiveMesh := ⟨1, by norm_num⟩
  let p := law (slitBoxGraph n) q (slitBoxBoundary n)
  let r := revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ)
  let S : Set (Configuration (slitBoxGraph n)) :=
    {A | A ∈ slitBoxWiredArcConnectionEvent n u ∧
      configurationIso (slitBoxGraphHorizontalReflectionIso n) A ∈
        slitBoxWiredArcConnectionEvent n u}
  let E : Set (Configuration (slitBoxGraph n)) :=
    slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)
  have hp : ∀ A, p A ≠ 0 := by
    intro A
    exact (law_pos (slitBoxGraph n) q (slitBoxBoundary n) A).ne'
  have hstable : ∀ A B, r A = r B → (A ∈ S ↔ B ∈ S) := by
    intro A B hrecord
    have h := slitBoxPairedGoodEvent_stable_under_record
      n hn u huY huX δ A B hrecord
    change (A ∈ slitBoxWiredArcConnectionEvent n u ∧
        configurationIso (slitBoxGraphHorizontalReflectionIso n) A ∈
          slitBoxWiredArcConnectionEvent n u) ↔
      (B ∈ slitBoxWiredArcConnectionEvent n u ∧
        configurationIso (slitBoxGraphHorizontalReflectionIso n) B ∈
          slitBoxWiredArcConnectionEvent n u) at h
    simpa [S] using h
  let c₀ : ℝ := 1 / (20 * (n : ℝ)^4)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc₀_nonneg : 0 ≤ c₀ := by positivity
  have hc₀_le_one : c₀ ≤ 1 := by
    dsimp [c₀]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 20 * (n : ℝ)^4)).2
    have hp₄ : (1 : ℝ) ≤ (n : ℝ)^4 := one_le_pow₀ hnR
    nlinarith
  have hcond : ∀ y : Set.range r,
      (∃ A, r A = y.1 ∧ A ∈ S) →
        c₀ ≤ ((finiteStatisticConditionalPMF p hp r y).toMeasure E).toReal := by
    intro y hy
    rcases hy with ⟨A, hAy, hAS⟩
    rcases hAS with ⟨hA, hAReflect⟩
    have hbound := slitBoxPairedGoodRecord_conditional_center_arc_lower_bound
      n hn u huY huX δ q A hA hAReflect
    have hrecordEq :
        (⟨r A, Set.mem_range_self A⟩ : Set.range r) = y := by
      exact Subtype.ext hAy
    have hbound' : c₀ ≤
        ((finiteStatisticConditionalPMF p hp r
          (⟨r A, Set.mem_range_self A⟩ : Set.range r)).toMeasure E).toReal := by
      simpa [c₀, p, r, E] using hbound
    rw [← hrecordEq]
    exact hbound'
  have hfiber := finiteConditional_event_lower_bound_on_good_fibers
    p hp r S E c₀ hstable hc₀_nonneg hc₀_le_one hcond
  have hmono : (p.toMeasure (S ∩ E)).toReal ≤ (p.toMeasure E).toReal := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (fun _ h => h.2)
  have hbound := hfiber.trans hmono
  have hS : S = slitBoxWiredArcConnectionEvent n u ∩
      slitBoxWiredArcConnectionEvent n (slitBoxGraphHorizontalReflectionIso n u) :=
    slitBoxPairedGoodEvent_eq_symmetricBottomPair n u
  rw [hS] at hbound
  change c₀ * (measure (slitBoxGraph n) q (slitBoxBoundary n)
      (slitBoxWiredArcConnectionEvent n u ∩
        slitBoxWiredArcConnectionEvent n (slitBoxGraphHorizontalReflectionIso n u))).toReal ≤
    (measure (slitBoxGraph n) q (slitBoxBoundary n)
      (slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n))).toReal at hbound
  erw [fkc_measure_eq] at hbound
  exact hbound

/-- Pair-to-center conversion throughout the full closed real range [1,4].
Only this unconditional finite-event inequality is passed to the endpoint. -/
theorem slit_center_probability_ge_pair
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (q : Set.Icc (1 : ℝ) 4) :
    (1 / (20 * (n : ℝ)^4)) * slitPairConnectionProbability n ⟨q, q.2.1⟩ u ≤
      slitArcConnectionProbability n ⟨q, q.2.1⟩ (slitBoxBottomCenterVertex n) := by
  apply continuous_le_on_closed_range _ _
    (continuous_const.mul (continuous_slitPairConnectionProbability n u))
    (continuous_slitArcConnectionProbability n (slitBoxBottomCenterVertex n)) _ q
  intro r hr
  exact slit_center_probability_ge_pair_strict n hn u huY huX ⟨r.val, r.property, hr⟩

end
end PottsContinuity.Thm4
