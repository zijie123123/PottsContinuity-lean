module

public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.FK.LimitTranslation

/-! Translation invariance for the frozen every-exhaustion limit. -/

@[expose] public section

namespace PottsContinuity.Infinite

open MeasureTheory

/-- Every frozen infinite-volume limit is invariant under lattice translations.
This uses the box specialization of the every-exhaustion hypothesis, while
retaining the original frozen hypothesis in the public statement. -/
theorem infinite_volume_translation_invariant
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q i μ)
    (a : PottsContinuity.PD.FK.LatticeVertex) :
    μ.map (PottsContinuity.PD.FK.latticeConfigurationTranslate a) = μ := by
  exact PottsContinuity.PD.FK.isRCInfiniteVolumeLimit_translation_invariant
    p q hq i μ (isRCInfiniteVolumeLimit_to_PD_box p q i μ hμ) a

end PottsContinuity.Infinite
