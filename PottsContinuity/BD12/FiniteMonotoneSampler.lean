module

public import PottsContinuity.BD12.FinitePinnedPattern

/-! The deterministic sequential threshold sampler used in DRT. Here the sampler
and its monotonicity are proved for every fixed reveal order. With fresh uniform
thresholds its output has the pinned conditional law: see
`finiteUniformRevealTreeLaw_eq_pinned` in `BD12.FiniteUniformTree`, matched to this
step by `finiteRevealPattern_uniformBit` in `BD12.JointHybridRegularity`. -/

@[expose] public section

namespace PottsContinuity.BD12

noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- One threshold update, using the actual conditional open probability.
Real inputs give the literal threshold map on the whole input carrier. -/
def finiteThresholdStep (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (u : ℝ) : Finset E :=
  if 1 - finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) ≤ u
    then insert e H else H.erase e

theorem finiteThresholdStep_monotone (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R : Finset E) {H K : Finset E} (hHK : H ⊆ K) (e : E)
    {u v : ℝ} (huv : u ≤ v) :
    finiteThresholdStep w R H e u ⊆ finiteThresholdStep w R K e v := by
  have hp := finitePinnedOpenProbability_monotone w hw R e hHK
  unfold finiteThresholdStep
  by_cases hH : 1 - finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) ≤ u
  · have hK : 1 - finitePinnedMean w R K (fun A => if e ∈ A then 1 else 0) ≤ v := by
      linarith
    simp only [ite_eq_left hH, ite_eq_left hK]
    exact Finset.insert_subset_insert e hHK
  · simp only [ite_eq_right hH]
    split_ifs
    · exact (Finset.erase_subset _ _).trans (hHK.trans (Finset.subset_insert _ _))
    · exact Finset.erase_subset_erase e hHK

end
end PottsContinuity.BD12
