module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.FiniteContractedAlternative
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.AlmostSureOpenColumns
public import PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers.AlmostSureConsumer
public import PottsContinuity.Thm3.Touch.InfiniteHalfHeightSlopeReflection

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 Thm3.Touch PD.FK PD.FK.Medial MeasureTheory
noncomputable section
local instance routeFourteenBondCountable : Countable LatticeBond :=
  Countable.of_equiv (LatticeVertex × LatticeAxis)
    { toFun := fun p => ⟨p.1,p.2⟩
      invFun := fun b => (b.base,b.axis)
      left_inv := by rintro ⟨a,x⟩; rfl
      right_inv := by rintro ⟨a,x⟩; rfl }
local instance routeFourteenReducedCountable (N : ℕ) (t : ℝ) :
    Countable (RSW.tiltedStripReducedCarrier N t) := by
  unfold RSW.tiltedStripReducedCarrier TiltedBond
  infer_instance


/-- The open-column estimate `ae_exists_fullyOpenColumns_both_sides` upgrades the
finite contracted-pair alternative to an almost-sure cover, without an independence
hypothesis. -/
theorem ae_halfHeight_or_native_dual_nonpositive
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 0) :
    ∀ᵐ ω ∂(selfDualTiltedStripMeasure q (2*n) t),
      lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n ∨
      RSW.tiltedStripReducedDualTransport (2*n) t (by exact ⟨ht.1,by linarith [ht.2]⟩)
        (RSW.tiltedStripReducedRestriction (2*n) t ω) ∈
          reducedCarrierHalfHeight n (by omega) t := by
  filter_upwards [ae_exists_fullyOpenColumns_both_sides q (2*n) t] with ω hω
  obtain ⟨xm,xp,hm,hp,hfm,hfp⟩ := hω
  exact halfHeight_or_native_dual_of_open_columns_nonpositive n hn t ht ω xm xp hm hp hfm hfp

/-- The entire geometric half-height argument on the nonpositive branch;
the sole remaining input is the exact reduced-carrier marginal identity `hlaw`. -/
theorem selfDualTiltedHalfHeight_nonpositive_ge_half_of_reducedMarginal
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 0)
    (hlaw : Measure.map
      (RSW.tiltedStripReducedDualTransport (2*n) t (by exact ⟨ht.1,by linarith [ht.2]⟩))
      (Measure.map (RSW.tiltedStripReducedRestriction (2*n) t)
        (selfDualTiltedStripMeasure q (2*n) t)) =
      Measure.map (RSW.tiltedStripReducedRestriction (2*n) t)
        (selfDualTiltedStripMeasure q (2*n) t)) :
    (1/2 : ℝ) ≤ (selfDualTiltedStripMeasure q (2*n) t).real
      {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n} := by
  have hs : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  let μ := selfDualTiltedStripMeasure q (2*n) t
  let R := RSW.tiltedStripReducedRestriction (2*n) t
  let D := RSW.tiltedStripReducedDualTransport (2*n) t hs
  let H : Set (TiltedConfiguration (2*n) t) :=
    {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n}
  let E := reducedCarrierHalfHeight n (by omega) t
  have hR := (RSW.tiltedStripReducedRestriction_continuous (2*n) t).measurable
  have hD := (RSW.tiltedStripReducedDualTransport_continuous (2*n) t hs).measurable
  have hE : MeasurableSet E := by
    rw [show E = reducedCarrierHalfHeight n (by omega) t from rfl,
      reducedCarrierHalfHeight_eq_iUnion n (by omega) t hs]
    exact MeasurableSet.iUnion fun r => (reducedCarrier_bounded_paths_isClopen n r t).isOpen.measurableSet
  have hmap : μ.map (D ∘ R) = μ.map R := by
    rw [←Measure.map_map hD hR]
    exact hlaw
  have hbalance : (μ.map R).real E = μ.real H := by
    unfold Measure.real
    rw [Measure.map_apply hR hE]
    rw [show R ⁻¹' E = H from halfHeight_reducedRestriction_preimage n (by omega) t]
  exact TiltedHalfHeightConsumers.probability_ge_half_of_ae_cover_and_map μ (μ.map R)
    (D ∘ R) (hD.comp hR) H E (TiltedHalfHeightConsumers.measurableSet_tiltedHalfHeight n hn t hs) hE
    (ae_halfHeight_or_native_dual_nonpositive q n hn t ht) hmap hbalance

/-- Exact source half-height conclusion at every slope. All geometry is
proved; the reduced-carrier marginal identity `hmarginal` is the only explicit input. -/
theorem selfDualTiltedHalfHeight_ge_half
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (hn : 1 ≤ n)
    (hmarginal : ∀ (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1),
      Measure.map (RSW.tiltedStripReducedDualTransport (2*n) s hs)
        (Measure.map (RSW.tiltedStripReducedRestriction (2*n) s)
          (selfDualTiltedStripMeasure q (2*n) s)) =
        Measure.map (RSW.tiltedStripReducedRestriction (2*n) s)
          (selfDualTiltedStripMeasure q (2*n) s))
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (1/2 : ℝ) ≤ (selfDualTiltedStripMeasure q (2*n) t).real
      {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n} := by
  by_cases hnon : t ≤ 0
  · exact selfDualTiltedHalfHeight_nonpositive_ge_half_of_reducedMarginal q n hn t
      ⟨ht.1,hnon⟩ (hmarginal t ht)
  · have hneg : -t ∈ Set.Icc (-1 : ℝ) 0 := by constructor <;> linarith [ht.1,ht.2]
    have hfull : -t ∈ Set.Icc (-1 : ℝ) 1 := ⟨hneg.1,by linarith [hneg.2]⟩
    have h := selfDualTiltedHalfHeight_nonpositive_ge_half_of_reducedMarginal q n hn (-t)
      hneg (hmarginal (-t) hfull)
    rw [selfDualTiltedHalfHeight_real_reflection q n hn t ht] at h
    exact h

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
