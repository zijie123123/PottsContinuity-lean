module

public import PottsContinuity.BD12.PositiveCentredOneArmSum
public import PottsContinuity.BD12.PositiveShellAverageOSSS
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! The positive finite centred one-arm covariance-sum estimate, with all exploration
and counting steps proved. The finite graph's metric data are explicit. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory FKC.FiniteFK
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
local instance positiveCentredCovEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveCentredCovEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The actual maximum one-arm sum contains its radius-zero term, whose
probability is one. Thus division by this maximum is justified for n>=1. -/
theorem positiveCentredOneArmMaximum_ge_one
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (d : V → V → ℕ) (n : ℕ) (hn : 1 ≤ n) (u : V) (hdu : d u u = 0) :
    1 ≤ positiveCentredOneArmMaximum G w d n := by
  have hzero : radiusOneArmIndicator G (d u) u 0 = fun _ => (1 : ℝ) := by
    funext A
    have hevent : ∃ b, b ∈ finiteRadiusShell (d u) 0 ∧ ActualConnected G A u b :=
      ⟨u, (mem_finiteRadiusShell (d u) 0 u).mpr hdu, ⟨.nil⟩⟩
    simp only [radiusOneArmIndicator, finiteConnectionToSetIndicator, ite_eq_left hevent]
  have hmean : finitePositiveMean w (radiusOneArmIndicator G (d u) u 0) = 1 := by
    rw [hzero]
    exact finitePositiveMean_one w
  have hsum : 1 ≤ positiveCentredOneArmSum G w d n u := by
    rw [← hmean]
    unfold positiveCentredOneArmSum
    apply Finset.single_le_sum (f := fun j => finitePositiveMean w (radiusOneArmIndicator G (d u) u j))
      (s := Finset.range n) (a := 0)
    · intro j _
      exact finitePositiveMean_nonneg w _
        (fun A => (finiteConnectionToSetIndicator_mem_Icc G u (finiteRadiusShell (d u) j) A).1)
    · simp only [Finset.mem_range]; omega
  exact hsum.trans (positiveCentredOneArmSum_le_maximum G w d n u)

variable [MeasurableSpace (PD.FK.Configuration G)] [MeasurableSingletonClass (PD.FK.Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- Centred one-arm version of the actual shell-averaged OSSS estimate, with
the factor four supplied by endpoints and the proved radius-counting bound. -/
theorem positive_connection_covariance_sum_mul_bound
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet))
    (r : V → ℕ) (d : V → V → ℕ)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (n : ℕ) (hr : ∀ u, r u ≤ n) (B : Finset V) (o : V) (ho : r o = 0) (hB : ∀ b ∈ B, n ≤ r b)
    (hd0 : ∀ u, d u u = 0) (hdstep : ∀ u {x y}, G.Adj x y → d u y ≤ d u x + 1)
    (hdom : ∀ u v, Nat.dist (r v) (r u) ≤ d u v)
    (ends₁ ends₂ : G.edgeSet → V) (hends : ∀ e, e.val = s(ends₁ e, ends₂ e))
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (hw : ∀ A D, (w A : ℝ) * w D ≤ (w (A ∩ D) : ℝ) * w (A ∪ D)) (U : ℕ → ℝ) :
    let f := finiteConnectionToSetIndicator G o B
    let θ := finitePositiveMean w f
    (n : ℝ) * (θ * (1 - θ)) ≤ 4 * positiveCentredOneArmMaximum G w d n *
      ∑ e, finitePositiveCovariance w f (fun A => if e ∈ A then 1 else 0) := by
  let f := finiteConnectionToSetIndicator G o B
  have hOSSS := positive_connection_osss_shell_average G rank r hstep n B o ho hB ends₁ ends₂ hends w hw U
  have hM := positiveShellConnectionMaximum_le_twice_centred G w r d n hr hd0 hdstep hdom
  have hc : 0 ≤ ∑ e, finitePositiveCovariance w f (fun A => if e ∈ A then (1 : ℝ) else 0) := by
    apply Finset.sum_nonneg
    intro e _
    let I := fun A : PD.FK.Configuration G => if e ∈ A then (1 : ℝ) else 0
    have hI0 : ∀ A, 0 ≤ I A := by intro A; dsimp [I]; split_ifs <;> norm_num
    have hIm : Monotone I := by
      intro A D hAD
      dsimp only [I]
      by_cases hA : e ∈ A
      · simp only [ite_eq_left hA, ite_eq_left (hAD hA), le_refl]
      · simp only [ite_eq_right hA]; split_ifs <;> norm_num
    exact finitePositiveCovariance_nonneg w hw f I
      (fun A => (finiteConnectionToSetIndicator_mem_Icc G o B A).1) hI0
      (finiteConnectionToSetIndicator_monotone G o B) hIm
  have h := hOSSS.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num)) hc)
  dsimp only
  convert h using 1; ring

/-- Covariance-sum lower bound with the source coefficient n/(4*M), where M
is the actual maximum centred one-arm sum. Positivity of M is proved above. -/
theorem positive_connection_covariance_sum_lower_bound
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet))
    (r : V → ℕ) (d : V → V → ℕ)
    (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (n : ℕ) (hn : 1 ≤ n) (hr : ∀ u, r u ≤ n) (B : Finset V) (o : V) (ho : r o = 0) (hB : ∀ b ∈ B, n ≤ r b)
    (hd0 : ∀ u, d u u = 0) (hdstep : ∀ u {x y}, G.Adj x y → d u y ≤ d u x + 1)
    (hdom : ∀ u v, Nat.dist (r v) (r u) ≤ d u v)
    (ends₁ ends₂ : G.edgeSet → V) (hends : ∀ e, e.val = s(ends₁ e, ends₂ e))
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (hw : ∀ A D, (w A : ℝ) * w D ≤ (w (A ∩ D) : ℝ) * w (A ∪ D)) (U : ℕ → ℝ) :
    let f := finiteConnectionToSetIndicator G o B
    let θ := finitePositiveMean w f
    ((n : ℝ) / (4 * positiveCentredOneArmMaximum G w d n)) * (θ * (1 - θ)) ≤
      ∑ e, finitePositiveCovariance w f (fun A => if e ∈ A then 1 else 0) := by
  have hM : 0 < 4 * positiveCentredOneArmMaximum G w d n := by
    have h := positiveCentredOneArmMaximum_ge_one G w d n hn o (hd0 o)
    linarith only [h]
  have h := positive_connection_covariance_sum_mul_bound G rank r d hstep n hr B o ho hB hd0 hdstep hdom
    ends₁ ends₂ hends w hw U
  dsimp only at h ⊢
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hM).mpr
  simpa only [mul_comm] using h

end
end PottsContinuity.BD12
