module

public import PottsContinuity.BD12.FiniteUniformTree
public import Mathlib.MeasureTheory.Measure.Prod

/-! Adaptive reveal orders may depend on past full uniform values and on an
auxiliary sequence, rather than only the revealed Boolean answers. Each node
draws a fresh uniform independent of its auxiliary probability law. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

/-- Complete fresh-coordinate reveal trees with auxiliary randomness.
Continuations see both real inputs, so they retain the full past information. -/
inductive AugmentedUniformRevealTree (E : Type*) [Fintype E] [DecidableEq E] :
    Finset E → Type _
  | done : AugmentedUniformRevealTree E Finset.univ
  | query {R : Finset E} (e : E) (he : e ∉ R)
      (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
      (next : ℝ × ℝ → AugmentedUniformRevealTree E (insert e R)) :
      AugmentedUniformRevealTree E R

noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace (Finset E)]

/-- Literal iterated independent sampling: the first real at each node is
uniform, the second has the specified auxiliary law, and both enter the past. -/
def augmentedUniformRevealTreeLaw (w : Finset E → Set.Ioi (0 : ℝ)) :
    {R : Finset E} → AugmentedUniformRevealTree E R → Finset E → Measure (Finset E)
  | _, .done, H => Measure.dirac H
  | R, .query e _he ν _hν next, H => (finiteUnitUniform.prod ν).bind (fun uv =>
      let b := finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) uv.1
      augmentedUniformRevealTreeLaw w (next uv) (finiteRevealPattern H e b))

/-- General fresh-input adaptive sampling law. The next edge may depend on
all past real inputs and auxiliary values, not just the past sampled bits. -/
theorem augmentedUniformRevealTreeLaw_eq_pinned (w : Finset E → Set.Ioi (0 : ℝ))
    {R : Finset E} (T : AugmentedUniformRevealTree E R) (H : Finset E) :
    augmentedUniformRevealTreeLaw w T H = (finitePinnedLaw w R H).toMeasure := by
  induction T generalizing H with
  | done =>
    rw [augmentedUniformRevealTreeLaw, finitePinnedLaw_univ, PMF.toMeasure_pure]
  | @query R e he ν hν next ih =>
    let : IsProbabilityMeasure ν := hν
    simp only [augmentedUniformRevealTreeLaw]
    simp_rw [ih]
    let f : Bool → Measure (Finset E) := fun b =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern H e b)).toMeasure
    have hf : Measurable (fun u =>
        f (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) u)) :=
      (measurable_of_finite f).comp (finiteUniformBit_measurable _)
    have hfst : (finiteUnitUniform.prod ν).map Prod.fst = finiteUnitUniform := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    have hreduce : (finiteUnitUniform.prod ν).bind (fun uv =>
          f (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) uv.1)) =
        finiteUnitUniform.bind (fun u =>
          f (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) u)) := by
      calc
        _ = ((finiteUnitUniform.prod ν).map Prod.fst).bind (fun u =>
            f (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) u)) := by
          unfold Measure.bind
          rw [Measure.map_map hf measurable_fst]
          rfl
        _ = _ := by rw [hfst]
    change (finiteUnitUniform.prod ν).bind (fun uv =>
      f (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) uv.1)) = _
    rw [hreduce, finiteUnitUniform_bind_reveal w R H e he f,
      finitePMF_toMeasure_bind, finitePinnedLaw_bind_reveal]

instance augmentedUniformRevealTreeLaw_isProbabilityMeasure
    (w : Finset E → Set.Ioi (0 : ℝ)) {R : Finset E}
    (T : AugmentedUniformRevealTree E R) (H : Finset E) :
    IsProbabilityMeasure (augmentedUniformRevealTreeLaw w T H) := by
  rw [augmentedUniformRevealTreeLaw_eq_pinned]
  infer_instance

end
end PottsContinuity.BD12
