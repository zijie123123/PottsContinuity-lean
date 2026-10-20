module

public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.Infinite.Parameters
public import PottsContinuity.Infinite.LocalComparisons

/-! Public comparison statements with the frozen every-exhaustion hypothesis. -/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Infinite

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

private theorem frozen_limit_to_pd
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q i μ) :
    PottsContinuity.PD.IsRCInfiniteVolumeLimit
      (pdParameters p q hp0 hp1 hq).toP (pdParameters p q hp0 hp1 hq).toQ i μ := by
  simpa only [pdParameters_toP, pdParameters_toQ] using
    isRCInfiniteVolumeLimit_to_PD_box p q i μ hμ

/-- The free infinite-volume law is stochastically dominated by the wired
infinite-volume law on local increasing events. -/
theorem free_infinite_le_wired_infinite_local
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : PottsContinuity.IsRCInfiniteVolumeLimit p q 0 μ₀)
    (hμ₁ : PottsContinuity.IsRCInfiniteVolumeLimit p q 1 μ₁)
    (m : ℕ) {A : Set LatticeConfiguration} (hA : IsCylinder A)
    (hdep : DependsOn (boxEdges (0, 0) m) A) (hupper : IsUpperSet A) :
    μ₀.real A ≤ μ₁.real A := by
  exact free_limit_le_wired_limit_local (pdParameters p q hp0 hp1 hq) μ₀ μ₁
    (frozen_limit_to_pd p q hp0 hp1 hq 0 μ₀ hμ₀)
    (frozen_limit_to_pd p q hp0 hp1 hq 1 μ₁ hμ₁) m hA hdep hupper

/-- Wired DMP comparison in the integrated exterior-cylinder form: for an
increasing event inside the box and any exterior cylinder event, the joint
probability is bounded by the wired box probability times the exterior
probability. -/
theorem wired_infinite_DMP_local
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q 1 μ)
    (m : ℕ) {A B : Set LatticeConfiguration}
    (hA : IsCylinder A) (hB : IsCylinder B)
    (hin : DependsOn (boxEdges (0, 0) m) A)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B)
    (hupper : IsUpperSet A) :
    μ.real (A ∩ B) ≤
      (boxMeasure (pdParameters p q hp0 hp1 hq) 1 (0, 0) m :
        Measure LatticeConfiguration).real A * μ.real B := by
  exact wired_limit_joint_le_local (pdParameters p q hp0 hp1 hq) μ
    (frozen_limit_to_pd p q hp0 hp1 hq 1 μ hμ) m hA hB hin hout hupper

end PottsContinuity.Infinite
