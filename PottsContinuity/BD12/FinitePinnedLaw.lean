module

public import PottsContinuity.BD12.FinitePinnedAssociation
public import PottsContinuity.PD.FK.Probability

/-! The genuine conditional PMF corresponding to finitePinnedMean.
Every partial Boolean pattern has positive mass under strictly positive weights. -/

@[expose] public section

namespace PottsContinuity.BD12

open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The actual finite law conditioned on the values H on the revealed set R. -/
def finitePinnedLaw (w : Finset E → Set.Ioi (0 : ℝ)) (R H : Finset E) : PMF (Finset E) :=
  PMF.ofFintype
    (fun A => ENNReal.ofReal (finitePinnedWeight w R H A / ∑ B, finitePinnedWeight w R H B))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun A _ =>
        div_nonneg (finitePinnedWeight_nonneg w R H A) (finitePinnedPartition_pos w R H).le)]
      rw [← Finset.sum_div, div_self (finitePinnedPartition_pos w R H).ne',
        ENNReal.ofReal_one])

theorem finitePinnedLaw_apply (w : Finset E → Set.Ioi (0 : ℝ)) (R H A : Finset E) :
    finitePinnedLaw w R H A =
      ENNReal.ofReal (finitePinnedWeight w R H A / ∑ B, finitePinnedWeight w R H B) := rfl

theorem finitePinnedLaw_apply_toReal (w : Finset E → Set.Ioi (0 : ℝ))
    (R H A : Finset E) :
    (finitePinnedLaw w R H A).toReal =
      finitePinnedWeight w R H A / ∑ B, finitePinnedWeight w R H B :=
  ENNReal.toReal_ofReal (div_nonneg (finitePinnedWeight_nonneg w R H A)
    (finitePinnedPartition_pos w R H).le)

theorem finitePinnedMean_eq_sum_law (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (f : Finset E → ℝ) :
    finitePinnedMean w R H f = ∑ A, (finitePinnedLaw w R H A).toReal * f A := by
  simp only [finitePinnedLaw_apply_toReal, div_mul_eq_mul_div, Finset.sum_div,
    finitePinnedMean]

theorem finitePinnedLaw_univ (w : Finset E → Set.Ioi (0 : ℝ)) (H : Finset E) :
    finitePinnedLaw w Finset.univ H = PMF.pure H := by
  have hz : (∑ A, finitePinnedWeight w Finset.univ H A) = (w H : ℝ) := by
    simp [finitePinnedWeight]
  ext A
  rw [finitePinnedLaw_apply, PMF.pure_apply, hz]
  by_cases h : A = H
  · subst A
    have hwH : (0 : ℝ) < w H := (w H).property
    simp [finitePinnedWeight, hwH.ne']
  · simp [finitePinnedWeight, h]

theorem finitePinnedLaw_empty (w : Finset E → Set.Ioi (0 : ℝ)) (H : Finset E) :
    finitePinnedLaw w ∅ H =
      PD.FK.FiniteProbability.pmf (fun A => (w A : ℝ)) (fun A => (w A).property) := by
  ext A
  change finitePinnedLaw w ∅ H A = ENNReal.ofReal ((w A : ℝ) / ∑ B, (w B : ℝ))
  simp only [finitePinnedLaw_apply, finitePinnedWeight, Finset.inter_empty, ite_true]

end
end PottsContinuity.BD12
