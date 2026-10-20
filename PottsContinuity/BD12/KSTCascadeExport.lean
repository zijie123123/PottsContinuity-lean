module

public import PottsContinuity.BD12.KSTCascade
public import PottsContinuity.PlanarTopology.KSTCascadeInclusion

/-! KST's wired cascade with the corridor geometry of `PlanarTopology.KSTCascadeInclusion`
discharged at integral scales divisible by twelve. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK

/-- The actual wired cascade relation has no geometry premise at these scales.
The divisibility hypotheses belong to the integral-scale construction of
`PlanarTopology.kst_corridor_bridge_inclusion`. -/
theorem wired_kst_cascade (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m l k : ℕ) (hml : l ≤ m) (hlk : k ≤ l) (hk : 1 ≤ k)
    (hl12 : 12 ∣ l) (hk12 : 12 ∣ k)
    (hq : 0 < μ.real (kstQuasiCrossing l k)) :
    1 - Real.sqrt (1 - μ.real (kstQuasiCrossing m l)) ≤
      max (μ.real (kstQuasiCrossing m k))
        ((1 - (1 - μ.real (kstBridge l)) ^ 2) / μ.real (kstQuasiCrossing l k)) :=
  wired_kst_cascade_of_kstCorridor θ μ hμ m l k hml hlk hk
    (PlanarTopology.kst_corridor_bridge_inclusion l k hl12 hk12 hlk hk) hq

end PottsContinuity.BD12
