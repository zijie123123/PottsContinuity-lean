module

public import PottsContinuity.Thm3.RSW.Lemma4CollarCoreBandReplay
public import PottsContinuity.Thm3.Push.BottomCoreBandProbability
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PlanarMixed.Square MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual residual-dual band probability dominates the ordinary
asymmetric three-side-wired rectangle band probability. The collar carrier,
core marginal, free leaves and sampled native walk are all discharged. -/
theorem lemma4_nativeBand_probability_ge_asymmetricRectangle
    (θ : Parameters) (n : ℕ) (hn : 1 ≤ n) :
    (measure (rectangleGraph (-56*(n:ℤ)-1,0) (112*n+1) (54*n)) θ
      (BoundaryCondition.wired
        {z : RectangleVertex (-56*(n:ℤ)-1,0) (112*n+1) (54*n) |
          z.val.1 = -56*(n:ℤ)-1 ∨ z.val.1 = -56*(n:ℤ)+((112*n:ℕ):ℤ) ∨
          z.val.2 = ((54*n:ℕ):ℤ)})
      (Push.rectangleBandConnectionEvent (-56*(n:ℤ)-1,0) (112*n+1) (n-1) (54*n)
        (by omega))).toReal ≤
    (measure (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)) θ
      (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1))
      (lemma4NativeDualBandEvent n)).toReal := by
  have hcore := Push.bottomCoreBand_probability_ge_rectangleBand θ
    (-56*(n:ℤ),0) (112*n) (54*n) (n-1) (by omega) (by omega)
  have hid := congrArg (fun μ =>
      (PMF.toMeasure μ (Push.bottomCoreBandEvent (-56*(n:ℤ),0) (112*n) (54*n) (n-1))).toReal)
    (bottomCollar_core_law_map (-56*(n:ℤ),0) (112*n) (54*n) θ)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hid
  have hsub : (bottomCollarCoreRestriction (-56*(n:ℤ),0) (112*n) (54*n)) ⁻¹'
      Push.bottomCoreBandEvent (-56*(n:ℤ),0) (112*n) (54*n) (n-1) ⊆
      lemma4NativeDualBandEvent n := fun D hD => lemma4_coreBand_replays_native n hn D hD
  have hmono :
      (measure (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)) θ
        (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1))
        ((bottomCollarCoreRestriction (-56*(n:ℤ),0) (112*n) (54*n)) ⁻¹'
          Push.bottomCoreBandEvent (-56*(n:ℤ),0) (112*n) (54*n) (n-1))).toReal ≤
      (measure (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)) θ
        (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1))
        (lemma4NativeDualBandEvent n)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  simpa only [Prod.fst,Prod.snd,zero_add] using hcore.trans (hid.symm.le.trans hmono)

end
end PottsContinuity.RSW
