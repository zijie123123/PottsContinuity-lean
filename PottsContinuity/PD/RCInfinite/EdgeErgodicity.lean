-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/RCInfinite/EdgeErgodicity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.FK.BoxTranslation
public import PottsContinuity.PD.Defs.IsTranslationErgodic
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK

/-- Translate a bond field by `a`; the new value at `e` is the old value at `e-a`. -/
abbrev edgeTranslate (a : LatticeVertex) : LatticeConfiguration ≃ LatticeConfiguration :=
  latticeConfigurationTranslate a

theorem edgeTranslate_measurable (a : LatticeVertex) : Measurable (edgeTranslate a) :=
  latticeConfigurationTranslate_measurable a

@[simp] theorem edgeTranslate_zero (ω : LatticeConfiguration) : edgeTranslate 0 ω = ω := by
  funext e
  have hz : latticeTranslate (0 : LatticeVertex) = id := funext latticeTranslate_zero
  simp [edgeTranslate, latticeConfigurationTranslate_apply, latticeTranslationIso,
    SimpleGraph.Iso.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet, hz]

theorem edgeTranslate_add (a b : LatticeVertex) (ω : LatticeConfiguration) :
    edgeTranslate (a + b) ω = edgeTranslate a (edgeTranslate b ω) := by
  funext e
  simp only [latticeConfigurationTranslate_apply]
  congr 1
  apply Subtype.ext
  simp only [SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
    Sym2.map_map]
  congr 1
  funext x
  ext <;> simp [latticeTranslationIso, latticeTranslate] <;> ring

/-- Translation invariance and the null-or-conull property for measurable
strictly invariant events of the original bond configuration. -/
def IsEdgeTranslationErgodic (μ : Measure LatticeConfiguration) : Prop :=
  (∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) ∧
    ∀ A : Set LatticeConfiguration, MeasurableSet A →
      (∀ a : LatticeVertex, (edgeTranslate a) ⁻¹' A = A) → μ A = 0 ∨ μ Aᶜ = 0

theorem IsEdgeTranslationErgodic.zero_one {μ : Measure LatticeConfiguration}
    [IsProbabilityMeasure μ] (hμ : IsEdgeTranslationErgodic μ)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hinv : ∀ a : LatticeVertex, (edgeTranslate a) ⁻¹' A = A) :
    μ A = 0 ∨ μ A = 1 := by
  rcases hμ.2 A hA hinv with h | h
  · exact Or.inl h
  · right
    have hadd := measure_add_measure_compl (μ := μ) hA
    simpa [h] using hadd

/-- An equivariant measurable map from an ergodic bond field to a site field
produces the exact frozen notion of site-field translation ergodicity. -/
theorem IsEdgeTranslationErgodic.factor {S : Type*} [MeasurableSpace S]
    {μ : Measure LatticeConfiguration} (hμ : IsEdgeTranslationErgodic μ)
    (F : LatticeConfiguration → (LatticeVertex → S)) (hF : Measurable F)
    (heq : ∀ a ω x, F (edgeTranslate a ω) x = F ω (x - a)) :
    IsTranslationErgodic (μ.map F) := by
  have hshift (a : LatticeVertex) : Measurable (fun σ : LatticeVertex → S => fun x => σ (x + a)) :=
    measurable_pi_iff.mpr (fun x => measurable_pi_apply (x + a))
  constructor
  · intro a
    rw [Measure.map_map (hshift a) hF]
    have hc : (fun σ : LatticeVertex → S => fun x => σ (x + a)) ∘ F =
        F ∘ edgeTranslate (-a) := by
      funext ω x
      simpa only [Function.comp_apply, sub_neg_eq_add] using (heq (-a) ω x).symm
    rw [hc, ← Measure.map_map hF (edgeTranslate_measurable (-a)), hμ.1 (-a)]
  · intro A hA hinv
    have hpre : ∀ a, (edgeTranslate a) ⁻¹' (F ⁻¹' A) = F ⁻¹' A := by
      intro a
      ext ω
      change F (edgeTranslate a ω) ∈ A ↔ F ω ∈ A
      have hc : F (edgeTranslate a ω) = fun x => F ω (x + -a) := by
        funext x
        simpa only [sub_eq_add_neg] using heq a ω x
      rw [hc]
      exact Set.ext_iff.mp (hinv (-a)) (F ω)
    rcases hμ.2 (F ⁻¹' A) (hF hA) hpre with h | h
    · left
      rwa [Measure.map_apply hF hA]
    · right
      rw [Measure.map_apply hF hA.compl]
      simpa only [Set.preimage_compl] using h

end PottsContinuity.PD.RCInfinite
