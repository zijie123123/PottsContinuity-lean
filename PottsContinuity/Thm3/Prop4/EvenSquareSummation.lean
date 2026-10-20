module

public import PottsContinuity.Thm3.RSW.ExteriorCircuitInfinite
public import PottsContinuity.Thm3.Prop4.PairKernel
public import Mathlib
public import PottsContinuity.Thm3.Prop4.ReweightedSummability
public import PottsContinuity.Thm3.Prop4.OddSquare
public import PottsContinuity.Thm3.Prop4.PrecedingTail
public import PottsContinuity.Thm3.Prop4.ArmMonotone

/-!
# Source-compatible odd/even grouping of the exterior-circuit tail

Pair 2m-1 with 2m, so the proved odd-square remark uses the same arm scale m.
Only the actual even-square Lemma-7 estimate remains as an explicit input.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- Consume the actual even-square pair estimate and the proved odd-square
comparison, retaining the source arm scale in every convolution. -/
theorem reweighted_summation_of_evenSquarePairBound (θ : PD.FK.Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (A c ε β : ℝ) (hA : 0 < A) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβ1 : β < 1)
    (hub : BddAbove (Set.range (fun k : ℕ => Real.exp ((k : ℝ)^β)*RSW.oneArmProbability μ k)))
    (hpair : ∀ m : ℕ, 1 ≤ m → RSW.maxSquarePairProbability θ (2*m) ≤
      A*prop4PairKernel c ε (RSW.oneArmProbability μ) m) :
    ∀ n : ℕ, 1 ≤ n →
      Real.exp (((2*n : ℕ) : ℝ)^β)*RSW.oneArmProbability μ (2*n) ≤
      Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, prop4ReweightedKernel
          (1152*A*(1+1/PD.RCInfinite.openEnergy θ)) c ε β
          (fun k => Real.exp ((k : ℝ)^β)*RSW.oneArmProbability μ k) m.1) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  let a := RSW.oneArmProbability μ
  let u : ℕ → ℝ := fun k => Real.exp ((k : ℝ)^β)*a k
  let ρ := PD.RCInfinite.openEnergy θ
  have hρ : 0 < ρ := PD.RCInfinite.openEnergy_pos θ
  let C := 1152*A*(1+1/ρ)
  have hC : 0 < C := by dsimp [C]; positivity
  let K := prop4ReweightedKernel C c ε β u
  let f : ℕ → ℝ := fun M => 72*(M : ℝ)^4*RSW.maxSquarePairProbability θ M
  have ha : ∀ k, 0 ≤ a k := fun _ => ENNReal.toReal_nonneg
  have hK : ∀ m, 0 ≤ K m := prop4ReweightedKernel_nonneg C c ε β u hC.le hc.le
    (fun k => mul_nonneg (Real.exp_nonneg _) (ha k))
  have hf : ∀ M, 0 ≤ f M := fun M => mul_nonneg (by positivity) (RSW.maxSquarePairProbability_nonneg θ M)
  have hpairSum (m : ℕ) (hm : 1 ≤ m) : f (2*m-1)+f (2*m) ≤ K m := by
    let P := prop4PairKernel c ε a m
    have hP : 0 ≤ P := prop4PairKernel_nonneg c ε a hc.le ha m
    have heven : RSW.maxSquarePairProbability θ (2*m) ≤ A*P := hpair m hm
    have hodd : RSW.maxSquarePairProbability θ (2*m-1) ≤ A*P/ρ := by
      have h := maxSquarePairProbability_le_next θ (2*m-1)
      have heq : 2*m-1+1=2*m := by omega
      rw [heq] at h
      exact h.trans (div_le_div_of_nonneg_right heven hρ.le)
    have hpow : ((2*m-1 : ℕ) : ℝ)^4 ≤ ((2*m : ℕ) : ℝ)^4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le (2*m) 1) 4
    have hsmall : f (2*m-1) ≤ 72*((2*m : ℕ) : ℝ)^4*(A*P/ρ) := by
      exact (mul_le_mul_of_nonneg_left hodd (by positivity)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity))
    have hlarge : f (2*m) ≤ 72*((2*m : ℕ) : ℝ)^4*(A*P) :=
      mul_le_mul_of_nonneg_left heven (by positivity)
    calc
      _ ≤ 72*((2*m : ℕ) : ℝ)^4*(A*P/ρ)+72*((2*m : ℕ) : ℝ)^4*(A*P) := add_le_add hsmall hlarge
      _ = C*(m : ℝ)^4*P := by dsimp [C]; push_cast; ring
      _ = K m := (prop4ReweightedKernel_eq_pairKernel C c ε β a m).symm
  intro n hn
  have hs : Summable (fun m : {m : ℕ // n ≤ m} => K m.1) :=
    prop4ReweightedKernel_tail_summable u (fun k => mul_nonneg (Real.exp_nonneg _) (ha k))
      hub C c ε β hC hc hε hεβ hβ1 n hn
  have hbound : ENNReal.ofReal (a (2*n)) ≤ ENNReal.ofReal (∑' m : {m : ℕ // n ≤ m}, K m.1) := by
    calc
      _ ≤ ENNReal.ofReal (a (2*n-1)) := ENNReal.ofReal_le_ofReal (oneArmProbability_antitone μ (Nat.sub_le _ _))
      _ ≤ ∑' M : {M : ℕ // 2*n-1 ≤ M}, ENNReal.ofReal (f M.1) :=
        RSW.exterior_circuit_infinite θ μ hμ (2*n-1) (by omega)
      _ = ∑' m : {m : ℕ // n ≤ m}, (ENNReal.ofReal (f (2*m.1-1))+ENNReal.ofReal (f (2*m.1))) :=
        tsum_precedingTail (fun M => ENNReal.ofReal (f M)) n hn
      _ ≤ ∑' m : {m : ℕ // n ≤ m}, ENNReal.ofReal (K m.1) := by
        apply ENNReal.tsum_le_tsum
        intro m
        rw [← ENNReal.ofReal_add (hf _) (hf _)]
        exact ENNReal.ofReal_le_ofReal (hpairSum m.1 (hn.trans m.2))
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun m : {m : ℕ // n ≤ m} => hK m.1) hs).symm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (ha _),ENNReal.toReal_ofReal (tsum_nonneg (fun m : {m : ℕ // n ≤ m} => hK m.1))] at hreal
  exact mul_le_mul_of_nonneg_left hreal (Real.exp_nonneg _)

end PottsContinuity.Thm3.Prop4
