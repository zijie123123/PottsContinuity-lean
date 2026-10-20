module

public import PottsContinuity.BD12.KSTHypotheses
public import PottsContinuity.Infinite.MeasurableFKG

/-! KST probability hypotheses for either frozen infinite-volume boundary
condition. This includes the free law arising as a wired law's planar dual. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK

/-- Both actual infinite-volume limits are associated on measurable upper events. -/
theorem limit_measurable_positive_association (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (A B : Set LatticeConfiguration) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  let : IsProbabilityMeasure μ := hμ.1
  have h : μ A * μ B ≤ μ (A ∩ B) := by
    fin_cases i
    · exact Infinite.free_infinite_FKG_measurable θ.toP θ.toQ
        (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property μ hμ A B hA hB hAu hBu
    · exact Infinite.wired_infinite_FKG_measurable θ.toP θ.toQ
        (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property μ hμ A B hA hB hAu hBu
  simpa only [Measure.real_def, ENNReal.toReal_mul] using
    ENNReal.toReal_mono (measure_ne_top μ (A ∩ B)) h

/-- Both boundary limits preserve event probabilities under box-preserving isometries. -/
theorem limit_isometry_preimage_real (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (e : PD.squareLattice ≃g PD.squareLattice)
    (he : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (A : Set LatticeConfiguration) (hA : MeasurableSet A) :
    μ.real (latticeConfigurationIsoHomeomorph e ⁻¹' A) = μ.real A := by
  have hi := Infinite.infinite_volume_latticeIso_invariant θ.toP θ.toQ
    (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property i μ hμ e he
  change (μ (latticeConfigurationIsoHomeomorph e ⁻¹' A)).toReal = (μ A).toReal
  rw [← Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable e) hA, hi]

end PottsContinuity.BD12
