module

public import PottsContinuity.BD12.FiniteRevealTree
public import PottsContinuity.BD12.FiniteUniformReveal

/-! The actual fresh-uniform adaptive tree sampler. Measure bind draws a new
independent unit uniform at each visited node before selecting its subtree. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

theorem finitePMF_toMeasure_bind {α Ω : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace Ω] (p : PMF α) (f : α → PMF Ω) :
    p.toMeasure.bind (fun a => (f a).toMeasure) = (p.bind f).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_finite _).aemeasurable,
    lintegral_fintype, PMF.toMeasure_bind_apply p f s hs, tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
  exact mul_comm _ _

noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace (Finset E)]

/-- Uniform-threshold sampling down a complete adaptive decision tree. Every
node uses the current actual conditional probability and a fresh uniform. -/
def finiteUniformRevealTreeLaw (w : Finset E → Set.Ioi (0 : ℝ)) :
    {R : Finset E} → FiniteRevealTree E R → Finset E → Measure (Finset E)
  | _, .done, H => Measure.dirac H
  | R, .query e _he next, H => finiteUnitUniform.bind (fun u =>
      let b := finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) u
      finiteUniformRevealTreeLaw w (next b) (finiteRevealPattern H e b))

/-- The adaptive uniform construction has exactly the pinned conditional law.
This proves its law without assuming a sampling representation or fixed order. -/
theorem finiteUniformRevealTreeLaw_eq_pinned (w : Finset E → Set.Ioi (0 : ℝ))
    {R : Finset E} (T : FiniteRevealTree E R) (H : Finset E) :
    finiteUniformRevealTreeLaw w T H = (finitePinnedLaw w R H).toMeasure := by
  induction T generalizing H with
  | done =>
    rw [finiteUniformRevealTreeLaw, finitePinnedLaw_univ, PMF.toMeasure_pure]
  | @query R e he next ih =>
    simp only [finiteUniformRevealTreeLaw]
    simp_rw [ih]
    rw [finiteUnitUniform_bind_reveal w R H e he
      (fun b => (finitePinnedLaw w (insert e R) (finiteRevealPattern H e b)).toMeasure),
      finitePMF_toMeasure_bind, finitePinnedLaw_bind_reveal]

instance finiteUniformRevealTreeLaw_isProbabilityMeasure
    (w : Finset E → Set.Ioi (0 : ℝ)) {R : Finset E}
    (T : FiniteRevealTree E R) (H : Finset E) :
    IsProbabilityMeasure (finiteUniformRevealTreeLaw w T H) := by
  rw [finiteUniformRevealTreeLaw_eq_pinned]
  infer_instance

end
end PottsContinuity.BD12
