module

public import PottsContinuity.BD12.FinitePinnedLaw
public import PottsContinuity.BD12.FinitePinnedClosedUpdate

/-! Exact one-edge disintegration of the pinned finite law. -/

@[expose] public section

namespace PottsContinuity.BD12

open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The open pattern after revealing the literal Boolean value of e. -/
def finiteRevealPattern (H : Finset E) (e : E) (b : Bool) : Finset E :=
  if b then insert e H else H.erase e

theorem finitePinnedPartition_reveal (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) :
    (∑ b : Bool, ∑ A, finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) A) =
      ∑ A, finitePinnedWeight w R H A := by
  rw [Fintype.sum_bool]
  simp only [finiteRevealPattern, Bool.false_eq_true, ite_false, ite_true]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun A _ => by
    rw [add_comm]
    exact finitePinnedWeight_closed_add_open w R H A e he)

/-- The actual conditional Boolean law of the next, unrevealed coordinate. -/
def finiteRevealBitLaw (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (_he : e ∉ R) : PMF Bool :=
  PD.FK.FiniteProbability.pmf
    (fun b => ∑ A, finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) A)
    (fun b => finitePinnedPartition_pos w (insert e R) (finiteRevealPattern H e b))

theorem finiteRevealBitLaw_apply (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) (b : Bool) :
    finiteRevealBitLaw w R H e he b = ENNReal.ofReal
      ((∑ A, finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) A) /
        ∑ A, finitePinnedWeight w R H A) := by
  change ENNReal.ofReal (_ / ∑ b : Bool, _) = _
  rw [finitePinnedPartition_reveal w R H e he]

theorem finiteRevealBitLaw_apply_toReal (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) (b : Bool) :
    (finiteRevealBitLaw w R H e he b).toReal =
      (∑ A, finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) A) /
        ∑ A, finitePinnedWeight w R H A := by
  rw [finiteRevealBitLaw_apply, ENNReal.toReal_ofReal]
  exact (div_pos (finitePinnedPartition_pos w _ _) (finitePinnedPartition_pos w R H)).le

/-- Sample the next Boolean value and then sample its conditional continuation:
the result has exactly the original pinned law, for arbitrary positive weights. -/
theorem finitePinnedLaw_bind_reveal (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) :
    (finiteRevealBitLaw w R H e he).bind
        (fun b => finitePinnedLaw w (insert e R) (finiteRevealPattern H e b)) =
      finitePinnedLaw w R H := by
  ext A
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ A) (PMF.apply_ne_top _ A)).mp
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (fun b _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ b) (PMF.apply_ne_top _ A))]
  simp only [ENNReal.toReal_mul, finiteRevealBitLaw_apply_toReal, finitePinnedLaw_apply_toReal]
  have hterm (b : Bool) :
      ((∑ B, finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) B) /
        ∑ B, finitePinnedWeight w R H B) *
      (finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) A /
        ∑ B, finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) B) =
      finitePinnedWeight w (insert e R) (finiteRevealPattern H e b) A /
        ∑ B, finitePinnedWeight w R H B := by
    field_simp [(finitePinnedPartition_pos w (insert e R) (finiteRevealPattern H e b)).ne']
  simp_rw [hterm]
  rw [← Finset.sum_div, Fintype.sum_bool]
  simp only [finiteRevealPattern, Bool.false_eq_true, ite_false, ite_true]
  rw [add_comm, finitePinnedWeight_closed_add_open w R H A e he]

end
end PottsContinuity.BD12
