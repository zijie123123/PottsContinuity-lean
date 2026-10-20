-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedGoodConditionalBound.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedConditionalEvent
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedCandidateComparison
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedRecordCandidates
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedRecordCenterCase
public import PottsContinuity.FKC.FiniteFK.PMFDiscreteMeasureInstanceIrrel
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory

noncomputable section

private theorem pairedGoodBound_inter_instance_irrel
    {α : Type*} (d₁ d₂ : DecidableEq α) (s t : Finset α) :
    @Inter.inter (Finset α) (@Finset.instInter α d₁) s t =
      @Inter.inter (Finset α) (@Finset.instInter α d₂) s t := by
  ext x
  simp only [Finset.mem_inter]

local instance pairedGoodBoundEdgeFintype (n : ℕ) : Fintype (slitBoxGraph n).edgeSet :=
  Fintype.ofFinite _
local instance pairedGoodBoundConfigFintype (n : ℕ) : Fintype (Configuration (slitBoxGraph n)) :=
  Fintype.ofFinite _
local instance pairedGoodBoundConfigNonempty (n : ℕ) : Nonempty (Configuration (slitBoxGraph n)) := ⟨∅⟩
local instance pairedGoodBoundConfigMeasurable (n : ℕ) : MeasurableSpace (Configuration (slitBoxGraph n)) := ⊤
local instance pairedGoodBoundConfigDiscrete (n : ℕ) : DiscreteMeasurableSpace (Configuration (slitBoxGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Every attained actual paired-good record has a uniformly positive
conditional probability of connecting the box center to the slit arc. The
conditional law is the exact fiber law of the original finite wired measure. -/
theorem slitBoxPairedGoodRecord_conditional_center_arc_lower_bound
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (δ : PositiveMesh) (q : ClusterWeight) (A : Configuration (slitBoxGraph n))
    (hA : A ∈ slitBoxWiredArcConnectionEvent n u)
    (hAReflect : configurationIso (slitBoxGraphHorizontalReflectionIso n) A ∈
      slitBoxWiredArcConnectionEvent n u) :
    (1 / (20 * (n : ℝ)^4) : ℝ) ≤
      ((finiteStatisticConditionalPMF
        (law (slitBoxGraph n) q (slitBoxBoundary n))
        (fun C => (law_pos (slitBoxGraph n) q (slitBoxBoundary n) C).ne')
        (revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ))
        ⟨revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ) A,
          Set.mem_range_self A⟩).toMeasure
        {C | C ∈ slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)}).toReal := by
  let R := slitBoxPairedReveal n hn u huY huX δ A
  let K := A ∩ R
  let r := revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ)
  have hK : K = @Inter.inter _ (@Finset.instInter _ (Classical.decEq _)) A R := by
    exact pairedGoodBound_inter_instance_irrel _ _ A R
  have hconditional := slitBoxPairedConditional_event_toReal_eq_remaining_restoration
    n hn u huY huX δ q A (slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n))
  have hcanonical :
      ((finiteStatisticConditionalPMF
        (law (slitBoxGraph n) q (slitBoxBoundary n))
        (fun C => (law_pos (slitBoxGraph n) q (slitBoxBoundary n) C).ne')
        (revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ))
        ⟨revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ) A,
          Set.mem_range_self A⟩).toMeasure
        (slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n))).toReal =
      (remainingMeasure (slitBoxGraph n) q
      (frozenBoundary (slitBoxBoundary n) K) R
      {B : RemainingConfiguration (slitBoxGraph n) R |
        B.val ∪ K ∈ slitBoxWiredArcConnectionEvent n
          (slitBoxBottomCenterVertex n)}).toReal := by
    refine hconditional.trans ?_
    let E₀ : Set (RemainingConfiguration (slitBoxGraph n) R) :=
      {B | @Union.union _ (@Finset.instUnion _ (Classical.decEq _)) B.val
          (@Inter.inter _ (@Finset.instInter _ (Classical.decEq _)) A
            (slitBoxPairedReveal n hn u huY huX δ A)) ∈
        slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)}
    let E₁ : Set (RemainingConfiguration (slitBoxGraph n) R) :=
      {B | B.val ∪ K ∈
        slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)}
    have hE : E₀ = E₁ := by
      ext B
      have hrestore : @Union.union _ (@Finset.instUnion _ (Classical.decEq _)) B.val
          (@Inter.inter _ (@Finset.instInter _ (Classical.decEq _)) A
            (slitBoxPairedReveal n hn u huY huX δ A)) = B.val ∪ K := by
        rw [← hK]
        ext e
        simp only [Finset.mem_union]
      exact Iff.of_eq (congrArg (fun C => C ∈
        slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)) hrestore)
    change ((remainingLaw (slitBoxGraph n) q
        (frozenBoundary (slitBoxBoundary n)
          (@Inter.inter _ (@Finset.instInter _ (Classical.decEq _) ) A
            (slitBoxPairedReveal n hn u huY huX δ A)))
        (slitBoxPairedReveal n hn u huY huX δ A)).toMeasure E₀).toReal =
      (remainingMeasure (slitBoxGraph n) q
        (frozenBoundary (slitBoxBoundary n) K) R E₁).toReal
    rw [hE, ← hK, remainingMeasure]
    let : Fintype (RemainingConfiguration (slitBoxGraph n) R) := Fintype.ofFinite _
    have dSubtype : @DiscreteMeasurableSpace
        (RemainingConfiguration (slitBoxGraph n) R) Subtype.instMeasurableSpace := by
      infer_instance
    have dTop : @DiscreteMeasurableSpace
        (RemainingConfiguration (slitBoxGraph n) R)
        (remainingConfigurationMeasurableSpace (slitBoxGraph n) R) := by
      let : MeasurableSpace (RemainingConfiguration (slitBoxGraph n) R) :=
        remainingConfigurationMeasurableSpace (slitBoxGraph n) R
      exact ⟨fun _ => MeasurableSpace.measurableSet_top⟩
    have hmeasureInstances := @pmf_toMeasure_apply_toReal_eq_of_discrete_instances
      (RemainingConfiguration (slitBoxGraph n) R) inferInstance
      (remainingLaw (slitBoxGraph n) q
        (frozenBoundary (slitBoxBoundary n) K) R
      )
      E₁ Subtype.instMeasurableSpace
        (remainingConfigurationMeasurableSpace (slitBoxGraph n) R)
      dSubtype dTop
    simp [R]
  have hconditionalNormalized := hcanonical
  change (1 / (20 * (n : ℝ)^4) : ℝ) ≤
    ((finiteStatisticConditionalPMF
      (law (slitBoxGraph n) q (slitBoxBoundary n))
      (fun C => (law_pos (slitBoxGraph n) q (slitBoxBoundary n) C).ne')
      (revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ))
      ⟨revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ) A,
        Set.mem_range_self A⟩).toMeasure
      (slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n))).toReal
  have hcanonicalBound : (1 / (20 * (n : ℝ)^4) : ℝ) ≤
      (remainingMeasure (slitBoxGraph n) q (frozenBoundary (slitBoxBoundary n) K) R
        {B : RemainingConfiguration (slitBoxGraph n) R |
          B.val ∪ K ∈ slitBoxWiredArcConnectionEvent n
            (slitBoxBottomCenterVertex n)}).toReal := by
    by_cases huZero : u.val.1 = 0
    · have hzero := slitBoxPairedRecord_zeroX_restores_center_arc
        n hn u huY huZero δ A hA hAReflect
      have hE : {B : RemainingConfiguration (slitBoxGraph n) R |
          B.val ∪ K ∈ slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)} =
          Set.univ := by
        ext B
        constructor
        · intro _
          trivial
        · intro _
          let A' := (edgeRestrictionConfigurationEquiv (slitBoxGraph n) R).symm B
          have hrest := slitBoxPairedRecord_zeroX_restores_center_arc
            n hn u huY huZero δ A hA hAReflect A'
          have hrestore : (edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A').val ∪ K ∈
              slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) := by
            change (edgeRestrictionConfigurationEquiv (slitBoxGraph n)
              (slitBoxPairedReveal n hn u huY huX δ A) A').val ∪
                (A ∩ slitBoxPairedReveal n hn u huY huX δ A) ∈ _
            exact hrest.2
          have hEq : edgeRestrictionConfigurationEquiv (slitBoxGraph n) R A' = B :=
            Equiv.apply_symm_apply _ _
          rw [hEq] at hrestore
          exact hrestore
      have hE' : {B : RemainingConfiguration (slitBoxGraph n) R |
          (B.val ∪ (A ∩ slitBoxPairedReveal n hn u huY huX δ A)) ∈
            slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)} = Set.univ := by
        simpa [K, R] using hE
      have hmeasure : remainingMeasure (slitBoxGraph n) q
          (frozenBoundary (slitBoxBoundary n) K) R
            {B : RemainingConfiguration (slitBoxGraph n) R |
            B.val ∪ K ∈ slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)} = 1 := by
          rw [hE]
          exact MeasureTheory.measure_univ
      have hmeasure' : (remainingMeasure (slitBoxGraph n) q
          (frozenBoundary (slitBoxBoundary n) K) R
            {B : RemainingConfiguration (slitBoxGraph n) R |
            B.val ∪ K ∈ slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n)}).toReal = 1 := by
          exact congrArg ENNReal.toReal hmeasure
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpow : (1 : ℝ) ≤ (n : ℝ)^4 := one_le_pow₀ hnR
      have hden : (1 : ℝ) ≤ 20 * (n : ℝ)^4 := by nlinarith
      have hc : (1 / (20 * (n : ℝ)^4) : ℝ) ≤ 1 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 20 * (n : ℝ)^4)).2
        simpa using hden
      exact le_trans hc (le_of_eq hmeasure'.symm)
    · have huPos : 0 < u.val.1 := lt_of_le_of_ne huX (Ne.symm huZero)
      let p := slitBoxLeastOpenCandidateOnEvent n hn u huY (le_of_lt huPos) δ A hA
      let qCandidate := slitBoxLeastOpenCandidateOnEvent n hn u huY (le_of_lt huPos) δ
        (configurationIso (slitBoxGraphHorizontalReflectionIso n) A) hAReflect
      have hCandidates := slitBoxPairedReveal_eq_candidates_on_good
        n hn u huY huPos δ A hA hAReflect
      have hpOpen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ K := by
        have := hCandidates.2.1
        simpa [K, R, p] using this
      have hqOpen : configurationIso (slitBoxGraphHorizontalReflectionIso n)
          (slitBoxCandidateOriginalPathEdgeSupport n u qCandidate) ⊆ K := by
        have hq : slitBoxCandidateOriginalPathEdgeSupport n
            (slitBoxReflectVertex n u) (slitBoxReflectCandidate n u qCandidate) ⊆ K := by
          simpa [K, R, qCandidate] using hCandidates.2.2
        rw [← slitBoxReflectCandidate_edgeSupport n u qCandidate] at hq
        exact hq
      have hbound := slitBoxPairedCandidate_restored_arc_probability_lower_bound
        n hn u huY huPos δ p qCandidate K hpOpen hqOpen q
      have hR : R = slitBoxPairedCandidateReveal n hn u huY huPos δ p qCandidate := by
        simpa only [R, p, qCandidate] using hCandidates.1
      rw [← hR] at hbound
      exact hbound

  exact le_trans hcanonicalBound (le_of_eq hcanonical.symm)
end

end PottsContinuity.FKC.FiniteFK

