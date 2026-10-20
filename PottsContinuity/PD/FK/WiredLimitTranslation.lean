-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/WiredLimitTranslation.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/FreeBoxTranslation.lean`.
Applied to the proved common wired-box limit and wired finite translation identity. -/
module

public import PottsContinuity.PD.FK.WiredBoxLimits
public import PottsContinuity.PD.FK.WiredBoxTranslation
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.PD.FK

noncomputable section

/-- The unique source-defined wired-box weak limit is invariant under every
integer translation of the original lattice configuration. -/
theorem wiredBoxLimit_translation_invariant (q : Parameters) (a : LatticeVertex) :
    ProbabilityMeasure.map
        (Classical.choose (PottsContinuity.PD.FK.wiredBoxLimit_existsUnique q))
        (latticeConfigurationTranslate a) =
      Classical.choose (PottsContinuity.PD.FK.wiredBoxLimit_existsUnique q) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (PottsContinuity.PD.FK.wiredBoxLimit_existsUnique q)
  have hproperty := (Classical.choose_spec (PottsContinuity.PD.FK.wiredBoxLimit_existsUnique q)).1
  have horigin : Tendsto (fun n => wiredBoxProbabilityMeasure q (0, 0) n) atTop (𝓝 μ) :=
    hproperty (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have hshift : Tendsto (fun n => wiredBoxProbabilityMeasure q a n) atTop (𝓝 μ) := by
    apply hproperty (fun _ => a) (fun n => n)
    · intro n
      exact latticeBox_mono a (Nat.le_succ n)
    · intro v
      obtain ⟨n, hn⟩ := origin_latticeBox_exhaustive (latticeTranslate (-a) v)
      refine ⟨n, ?_⟩
      simpa [latticeTranslate] using
        (mem_latticeBox_translate_iff a (0, 0) (latticeTranslate (-a) v) n).mpr hn
  have hmap : Tendsto
      (fun n => ProbabilityMeasure.map (wiredBoxProbabilityMeasure q (0, 0) n)
        (latticeConfigurationTranslate a)) atTop
      (𝓝 (ProbabilityMeasure.map μ (latticeConfigurationTranslate a))) :=
    ((ProbabilityMeasure.continuous_map
      (latticeConfigurationTranslationHomeomorph a).continuous_toFun).continuousAt.tendsto).comp
      horigin
  have hterms :
      (fun n => ProbabilityMeasure.map (wiredBoxProbabilityMeasure q (0, 0) n)
        (latticeConfigurationTranslate a)) =
      (fun n => wiredBoxProbabilityMeasure q a n) := by
    funext n
    simpa [latticeTranslate] using wiredBoxProbabilityMeasure_translation_map q a (0, 0) n
  rw [hterms] at hmap
  have hEq := tendsto_nhds_unique hmap hshift
  simpa [μ] using hEq

end
end PottsContinuity.PD.FK
