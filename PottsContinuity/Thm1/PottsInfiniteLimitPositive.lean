module

public import PottsContinuity.Thm1.FiniteESSpinMeasure
public import PottsContinuity.Thm1.FiniteESCylinderLimit
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.FK.BoxExhaustion
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Clopen

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

private lemma pottsESSpinCylinder_isClopen (q : ℕ) (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q) :
    IsClopen {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} := by
  rw [show {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} =
    ⋂ x ∈ A, {σ : ℤ × ℤ → Fin q | σ x = ξ x} by ext σ; simp]
  apply isClopen_biInter_finset
  intro x hx
  have hEq : {σ : ℤ × ℤ → Fin q | σ x = ξ x} =
      (fun σ : ℤ × ℤ → Fin q => σ x) ⁻¹' ({ξ x} : Set (Fin q)) := by
    ext σ
    simp
  rw [hEq]
  exact (isClopen_discrete ({ξ x} : Set (Fin q))).preimage (continuous_apply x)



theorem exists_isPottsInfiniteVolumeLimit_pos
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q) :
    ∃ μ : Measure (ℤ × ℤ → Fin q), IsPottsInfiniteVolumeLimit q β i μ := by
  classical
  let θ := pottsESParameters q β hq hβ
  have hqθ : 1 ≤ (θ.toQ : ℝ) := by
    change 1 ≤ θ.val
    exact θ.property
  obtain ⟨ν, hν⟩ := Foundations.exists_isRCInfiniteVolumeLimit
    θ.toP θ.toQ hqθ (1 : Fin 2)
  let boxes : ℕ → Finset (ℤ × ℤ) := fun n => latticeBox (0, 0) n
  let μboxes : ℕ → ProbabilityMeasure (ℤ × ℤ → Fin q) :=
    fun n => pottsESFiniteSpinProbabilityMeasure (boxes n) q hq β hβ.le i
  obtain ⟨μlim, ψ, hψ, hψlim⟩ := CompactSpace.tendsto_subseq μboxes
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hRC : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 ν :=
    PottsContinuity.Infinite.isRCInfiniteVolumeLimit_to_PD_box
      θ.toP θ.toQ 1 ν (by simpa [θ] using hν)
  have hCylinderValue (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q) :
      (μlim : Measure (ℤ × ℤ → Fin q)).real
        {σ | ∀ x ∈ A, σ x = ξ x} =
      ∑ s : pottsESStatusSignature A,
        ν.real (pottsESConnectionInfiniteFullSignatureEvent
          (pottsESStatusPositivePairs A s)
          (pottsESStatusNegativePairs A s)
          (pottsESStatusGhostPositive A s)
          (pottsESStatusGhostNegative A s)) *
        pottsESStatusPatternFunctional hq i ξ A s := by
    let event : Set (ℤ × ℤ → Fin q) := {σ | ∀ x ∈ A, σ x = ξ x}
    have hEvent : IsClopen event := by
      simpa [event] using pottsESSpinCylinder_isClopen q A ξ
    let f : BoundedContinuousFunction (ℤ × ℤ → Fin q) ℝ :=
      BoundedContinuousFunction.indicator event hEvent
    have hInt (ρ : ProbabilityMeasure (ℤ × ℤ → Fin q)) :
        ∫ σ, f σ ∂(ρ : Measure (ℤ × ℤ → Fin q)) =
          (ρ : Measure (ℤ × ℤ → Fin q)).real event := by
      change ∫ σ, event.indicator 1 σ ∂(ρ : Measure (ℤ × ℤ → Fin q)) = _
      exact integral_indicator_one hEvent.1.measurableSet
    let limitValue := ∑ s : pottsESStatusSignature A,
        ν.real (pottsESConnectionInfiniteFullSignatureEvent
          (pottsESStatusPositivePairs A s)
          (pottsESStatusNegativePairs A s)
          (pottsESStatusGhostPositive A s)
          (pottsESStatusGhostNegative A s)) *
        pottsESStatusPatternFunctional hq i ξ A s
    have hBoxes : Tendsto
        (fun n => pottsEventProb (boxes n) β i
          (fun σ => ∀ x ∈ A, σ x = ξ x)) atTop (𝓝 limitValue) := by
      exact pottsES_pottsCylinder_probability_tendsto q hq β hβ i A ξ boxes
        (fun n => origin_latticeBox_nested n)
        (fun x => origin_latticeBox_exhaustive x) ν hRC
    have hWeakInt :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hψlim) f
    have hWeakInt' : Tendsto
        (fun k => ∫ σ, f σ ∂(μboxes (ψ k) : Measure (ℤ × ℤ → Fin q))) atTop
        (𝓝 (∫ σ, f σ ∂(μlim : Measure (ℤ × ℤ → Fin q)))) := by
      simpa only [Function.comp_apply] using hWeakInt
    have hSubsequence : Tendsto
        (fun k => pottsEventProb (boxes (ψ k)) β i
          (fun σ => ∀ x ∈ A, σ x = ξ x)) atTop
        (𝓝 ((μlim : Measure (ℤ × ℤ → Fin q)).real event)) := by
      have hEq (k : ℕ) :
          ∫ σ, f σ ∂(μboxes (ψ k) : Measure (ℤ × ℤ → Fin q)) =
          pottsEventProb (boxes (ψ k)) β i
            (fun σ => ∀ x ∈ A, σ x = ξ x) := by
        calc
          _ = (μboxes (ψ k) : Measure (ℤ × ℤ → Fin q)).real event := hInt _
          _ = _ := pottsESFiniteSpinProbabilityMeasure_cylinder
            (boxes (ψ k)) A q hq β hβ.le i ξ
      have hIntegralLimit := hWeakInt'.congr' (Filter.Eventually.of_forall hEq)
      simpa only [hInt μlim] using hIntegralLimit
    have hSubBoxes := hBoxes.comp hψtop
    have hValue :
        (μlim : Measure (ℤ × ℤ → Fin q)).real event = limitValue :=
      tendsto_nhds_unique hSubsequence hSubBoxes
    simpa [event, limitValue] using hValue
  refine ⟨(μlim : Measure (ℤ × ℤ → Fin q)), ?_⟩
  unfold IsPottsInfiniteVolumeLimit
  constructor
  · infer_instance
  · intro G hG hExhaust A ξ
    have hScalar := pottsES_pottsCylinder_probability_tendsto q hq β hβ i A ξ G
      (fun n => hG (Nat.le_succ n)) hExhaust ν hRC
    rw [hCylinderValue A ξ]
    exact hScalar


end

end PottsContinuity.Thm1
