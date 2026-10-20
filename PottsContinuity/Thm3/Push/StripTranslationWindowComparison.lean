module

public import PottsContinuity.Thm3.Push.StripTranslationWindowStates

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- An increasing strip event in a smaller centred window is dominated by
its literal translated event in any larger window containing that translate. -/
theorem stripWindowEventProbability_le_translation (θ : Parameters) (n m M : ℕ)
    (a : ℤ) (hfit : |a|+(m:ℤ) ≤ (M:ℤ))
    (E : Set (RSW.StripConfiguration n)) (hE : IsUpperSet E) :
    RSW.stripWindowEventProbability θ n m E ≤
      RSW.stripWindowEventProbability θ n M ((stripTranslation n a) ⁻¹' E) := by
  let G := PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ))
  let H := PottsContinuity.squareLattice.induce (RSW.stripWindow n M : Set (ℤ × ℤ))
  let f := stripWindowTranslationEmbedding n m M a hfit
  let S : Set (Configuration G) :=
    {C | RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C) ∈ E}
  have hS : IsUpperSet S := by
    intro C D hCD hC
    apply hE (fun e => RSW.stripWindowPlaneConfiguration_mono n m hCD
      ((RSW.stripPlaneEmbedding n).mapEdgeSet e)) hC
  have hcompare := RSW.embedded_boundary_probability_le G H f
    (stripWindowTranslation_map_le n m M a hfit) θ (RSW.stripWindowBoundary n M 0) S hS
  have hlaw : law G θ (isolatedExtensionPullbackBoundary f (RSW.stripWindowBoundary n M 0)) =
      law G θ (RSW.stripWindowBoundary n m 0) :=
    law_eq_of_boundary_partition_eq θ _ _ (stripWindowTranslation_top_partition n m M a hfit)
  unfold PD.FK.measure at hcompare
  rw [hlaw] at hcompare
  apply hcompare.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro C hC
  exact hE (stripWindow_translation_restriction_le n m M a hfit C) hC

end
end PottsContinuity.Push
