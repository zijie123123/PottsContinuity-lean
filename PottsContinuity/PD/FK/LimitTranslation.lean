-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/LimitTranslation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.FK.BoxLimits
public import PottsContinuity.PD.FK.FreeBoxTranslation
public import PottsContinuity.PD.FK.WiredLimitTranslation
public import PottsContinuity.PD.Infra.CylinderUniqueness
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Translation invariance on the exact frozen carrier

Uniqueness of the frozen cylinder characterization transfers the invariance of
the canonical free and wired limits to every measure satisfying that
characterization. The endpoint measures are invariant Dirac measures.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.PD.FK

noncomputable section

theorem dirac_constant_translation_invariant (b : Bool) (a : LatticeVertex) :
    (Measure.dirac (fun _ : squareLattice.edgeSet => b)).map
      (latticeConfigurationTranslate a) = Measure.dirac (fun _ => b) := by
  rw [Measure.map_dirac]
  congr 1
  funext e
  rw [latticeConfigurationTranslate_apply]

/-- Every interior-parameter frozen limit is invariant under every lattice translation. -/
theorem isRCInfiniteVolumeLimit_interior_translation_invariant
    (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) (a : LatticeVertex) :
    μ.map (latticeConfigurationTranslate a) = μ := by
  fin_cases i
  · let ν := Classical.choose (freeBoxLimit_existsUnique θ)
    have hν := (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
    have heq : μ = ν.toMeasure := rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ
      (isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hν)
    rw [heq]
    exact congrArg ProbabilityMeasure.toMeasure
      (Internal.freeBoxLimit_translation_invariant θ a)
  · let ν := Classical.choose (wiredBoxLimit_existsUnique θ)
    have hν := (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n)
      origin_latticeBox_nested origin_latticeBox_exhaustive
    have heq : μ = ν.toMeasure := rc_limit_unique θ.toP θ.toQ 1 μ ν.toMeasure hμ
      (isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ ν hν)
    rw [heq]
    exact congrArg ProbabilityMeasure.toMeasure (wiredBoxLimit_translation_invariant θ a)

/-- Translation invariance of every frozen box limit, including both endpoint parameters. -/
theorem isRCInfiniteVolumeLimit_translation_invariant
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (i : Fin 2)
    (μ : Measure (PottsContinuity.PD.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q i μ) (a : LatticeVertex) :
    μ.map (latticeConfigurationTranslate a) = μ := by
  by_cases hp0 : (p : ℝ) = 0
  · have hp : p = endpointParameter false := Subtype.ext hp0
    subst p
    have heq := rc_limit_unique (endpointParameter false) q i μ
      (Measure.dirac (fun _ => false)) hμ (isRCInfiniteVolumeLimit_endpoint q i false)
    rw [heq]
    exact dirac_constant_translation_invariant false a
  by_cases hp1 : (p : ℝ) = 1
  · have hp : p = endpointParameter true := Subtype.ext hp1
    subst p
    have heq := rc_limit_unique (endpointParameter true) q i μ
      (Measure.dirac (fun _ => true)) hμ (isRCInfiniteVolumeLimit_endpoint q i true)
    rw [heq]
    exact dirac_constant_translation_invariant true a
  let θ : Parameters :=
    { val := q
      property := hq
      edgeProbability := ⟨p, lt_of_le_of_ne p.property.1 (Ne.symm hp0),
        lt_of_le_of_ne p.property.2 hp1⟩ }
  exact isRCInfiniteVolumeLimit_interior_translation_invariant θ i μ hμ a

end

end PottsContinuity.PD.FK
