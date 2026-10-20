-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/FreeBoxDihedral.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/FreeBoxDihedral.lean`.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsContinuity.PD.FK.FreeBoxLimitV1
public import PottsContinuity.PD.Duality.BoxDihedral
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.PD.FK.Internal

noncomputable section

/-- A lattice graph isomorphism preserving centered box radii preserves the
unique weak limit of all nested exhaustive free-box laws. -/
theorem freeBoxLimit_latticeIso_invariant
    (q : Parameters) (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    ProbabilityMeasure.map
        (Classical.choose (PottsContinuity.PD.FK.freeBoxLimit_existsUnique q))
        (latticeConfigurationIsoHomeomorph e) =
      Classical.choose (PottsContinuity.PD.FK.freeBoxLimit_existsUnique q) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (PottsContinuity.PD.FK.freeBoxLimit_existsUnique q)
  let ν : ProbabilityMeasure LatticeConfiguration :=
    ProbabilityMeasure.map μ (latticeConfigurationIsoHomeomorph e)
  have hproperty :=
    (Classical.choose_spec (PottsContinuity.PD.FK.freeBoxLimit_existsUnique q)).1
  have hboxInvCenter (c v : LatticeVertex) (r : ℕ) :
      e v ∈ latticeBox c r ↔ v ∈ latticeBox (e.symm c) r := by
    have hh := hbox (e.symm c) v r
    simpa using hh
  have hνproperty :
      ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
        (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
        (∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) →
        Tendsto (fun n => boxProbabilityMeasure q (c n) (r n)) atTop (𝓝 ν) := by
    intro c r hnest hexhaust
    have htransformed : ∀ n,
        latticeBox (e.symm (c n)) (r n) ⊆
          latticeBox (e.symm (c (n + 1))) (r (n + 1)) := by
      intro n v hv
      exact (hboxInvCenter (c (n + 1)) v (r (n + 1))).mp (hnest n
        ((hboxInvCenter (c n) v (r n)).mpr hv))
    have hexhaustTransformed : ∀ v : LatticeVertex,
        ∃ n, v ∈ latticeBox (e.symm (c n)) (r n) := by
      intro v
      obtain ⟨n, hn⟩ := hexhaust (e v)
      refine ⟨n, ?_⟩
      exact (hboxInvCenter (c n) v (r n)).mp hn
    have hμ : Tendsto
        (fun n => boxProbabilityMeasure q (e.symm (c n)) (r n)) atTop (𝓝 μ) :=
      hproperty (fun n => e.symm (c n)) r htransformed hexhaustTransformed
    have hmap : Tendsto
        (fun n => ProbabilityMeasure.map
          (boxProbabilityMeasure q (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) atTop (𝓝 ν) :=
      ((ProbabilityMeasure.continuous_map
        (latticeConfigurationIsoHomeomorph e).continuous_toFun).continuousAt.tendsto).comp hμ
    have hterms :
        (fun n => ProbabilityMeasure.map
          (boxProbabilityMeasure q (e.symm (c n)) (r n))
          (latticeConfigurationIsoHomeomorph e)) =
        (fun n => boxProbabilityMeasure q (c n) (r n)) := by
      funext n
      simpa using boxProbabilityMeasure_iso_map q e hbox (e.symm (c n)) (r n)
    rw [hterms] at hmap
    exact hmap
  have huniq :=
    (Classical.choose_spec (PottsContinuity.PD.FK.freeBoxLimit_existsUnique q)).2 ν hνproperty
  simpa [μ, ν] using huniq

end
end PottsContinuity.PD.FK.Internal
