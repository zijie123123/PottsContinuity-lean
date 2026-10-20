module

public import PottsContinuity.Thm3.RSW.ExteriorCircuitInfinite
public import PottsContinuity.Thm3.Prop4.StretchedSummability
public import PottsContinuity.Thm3.Prop4.UniformTail

/-!
# The weighted-tail step in Proposition 3

DCST TeX line 1536. A stretched-exponential bound on opposite-square-side
pairs implies the same type of bound on the infinite-volume arm, with a finite
prefactor. Every series is proved summable before conversion from ENNReal.
The model-specific pair decay is retained as an explicit conditional input.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Filter Topology
noncomputable section

/-- The actual 72m^4 stretched-exponential tail, with summability at every
starting index and a positive finite prefactor uniform in that index. -/
theorem squarePair_stretched_tail_bound (d r : ℝ) (hd : 0 < d) (hr : 0 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      Summable (fun m : {m : ℕ // n ≤ m} =>
        72 * (m.val : ℝ)^4 * Real.exp (-d * (m.val : ℝ)^r)) ∧
      (∑' m : {m : ℕ // n ≤ m},
        72 * (m.val : ℝ)^4 * Real.exp (-d * (m.val : ℝ)^r)) ≤
        K * Real.exp (-(d/2) * (n : ℝ)^r) := by
  let g (m : ℕ) := 72 * (m : ℝ)^4 * Real.exp (-d * (m : ℝ)^r)
  let w (m : ℕ) := Real.exp ((d/2) * (m : ℝ)^r)
  have hg : ∀ m, 0 ≤ g m := fun m => by dsimp [g]; positivity
  have hw : Monotone w := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (half_pos hd).le
    exact Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) hr.le
  have heq (m : ℕ) : w m * g m =
      72 * (m : ℝ)^4 * Real.exp (-(d/2) * (m : ℝ)^r) := by
    change Real.exp _ * (72 * (m : ℝ)^4 * Real.exp _) = _
    calc
      _ = 72 * (m : ℝ)^4 * (Real.exp ((d/2) * (m : ℝ)^r) *
          Real.exp (-d * (m : ℝ)^r)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hs : Summable (fun m : ℕ => 72 * (m : ℝ)^4 *
      Real.exp (-(d/2) * (m : ℝ)^r)) := by
    have h := (Thm3.Prop4.summable_rpow_mul_stretched_exp 4 (d/2) r (half_pos hd) hr).mul_left 72
    simpa only [Real.rpow_ofNat, mul_assoc] using h
  have hweighted : Summable (fun m => w m * g m) := hs.congr (fun m => (heq m).symm)
  let K := 1 + ∑' m : ℕ, w m * g m
  have htotal : 0 ≤ ∑' m : ℕ, w m * g m :=
    tsum_nonneg (fun m => mul_nonneg (Real.exp_nonneg _) (hg m))
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n
  have hsum := Thm3.Prop4.summable_tail_of_weighted g w hg hw hweighted n (Real.exp_pos _)
  have htail := Thm3.Prop4.weighted_tail_le_tsum g w hg (fun m => Real.exp_nonneg _) hw hweighted n
  have htailK : w n * (∑' m : {m : ℕ // n ≤ m}, g m.val) ≤ K :=
    htail.trans (by dsimp [K]; linarith only)
  refine ⟨hsum, ?_⟩
  have hdiv : (∑' m : {m : ℕ // n ≤ m}, g m.val) ≤ K / w n :=
    (le_div_iff₀ (show 0 < w n from Real.exp_pos _)).mpr
      (by simpa only [mul_comm] using htailK)
  simpa only [g, w, div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hdiv

/-- Explicit square-pair stretched decay gives an actual infinite-arm bound.
The pair-decay premise is the remaining model-specific source step, not an
assumed bound on the arm itself. -/
theorem oneArm_stretched_bound_of_squarePairDecay (θ : Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (d r : ℝ) (hd : 0 < d) (hr : 0 < r)
    (hpair : ∀ m : ℕ, 1 ≤ m → maxSquarePairProbability θ m ≤
      Real.exp (-d * (m : ℝ)^r)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      oneArmProbability μ n ≤ K * Real.exp (-(d/2) * (n : ℝ)^r) := by
  obtain ⟨K, hK, htail⟩ := squarePair_stretched_tail_bound d r hd hr
  refine ⟨K, hK, ?_⟩
  intro n hn
  have hbound : ENNReal.ofReal (oneArmProbability μ n) ≤
      ENNReal.ofReal (K * Real.exp (-(d/2) * (n : ℝ)^r)) := by
    calc
      _ ≤ ∑' m : {m : ℕ // n ≤ m},
          ENNReal.ofReal (72 * (m.val : ℝ)^4 * maxSquarePairProbability θ m.val) :=
        exterior_circuit_infinite θ μ hμ n hn
      _ ≤ ∑' m : {m : ℕ // n ≤ m},
          ENNReal.ofReal (72 * (m.val : ℝ)^4 * Real.exp (-d * (m.val : ℝ)^r)) := by
        apply ENNReal.tsum_le_tsum
        intro m
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (hpair m.val (hn.trans m.property))
          (by positivity)
      _ = ENNReal.ofReal (∑' m : {m : ℕ // n ≤ m},
          72 * (m.val : ℝ)^4 * Real.exp (-d * (m.val : ℝ)^r)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (htail n).1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (htail n).2
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ oneArmProbability μ n from ENNReal.toReal_nonneg),
    ENNReal.toReal_ofReal (mul_nonneg hK.le (Real.exp_nonneg _))] using hreal

end
end PottsContinuity.RSW
