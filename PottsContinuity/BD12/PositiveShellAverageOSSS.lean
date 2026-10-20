module

public import PottsContinuity.BD12.PositiveShellConnectionMaximum
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! Average the actual boundary-seed explorations over shells 1,...,n.
The maximum is a defined finite maximum of actual shell-connection sums. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
local instance positiveShellAvgEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveShellAvgEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
variable [MeasurableSpace (PD.FK.Configuration G)] [MeasurableSingletonClass (PD.FK.Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- Averaged connection OSSS before the centred one-arm comparison. Every
exploration and revealment estimate is discharged. The factor two comes from
the two endpoints of each edge; shell sums have their actual finite maximum. -/
theorem positive_connection_osss_shell_average
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet))
    (r : V → ℕ) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (n : ℕ) (B : Finset V) (o : V) (ho : r o = 0) (hB : ∀ b ∈ B, n ≤ r b)
    (ends₁ ends₂ : G.edgeSet → V) (hends : ∀ e, e.val = s(ends₁ e, ends₂ e))
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (hw : ∀ A D, (w A : ℝ) * w D ≤ (w (A ∩ D) : ℝ) * w (A ∪ D)) (U : ℕ → ℝ) :
    let f := finiteConnectionToSetIndicator G o B
    let θ := finitePositiveMean w f
    (n : ℝ) * (θ * (1 - θ)) ≤
      2 * positiveShellConnectionMaximum G w r n *
        ∑ e, finitePositiveCovariance w f (fun A => if e ∈ A then 1 else 0) := by
  let f := finiteConnectionToSetIndicator G o B
  let θ := finitePositiveMean w f
  let c := fun e => finitePositiveCovariance w f (fun A => if e ∈ A then (1 : ℝ) else 0)
  let P := fun k u => finitePositiveMean w (fun A =>
    if FKC.FiniteFK.actualMultiClusterConnected G (finiteRadiusShell r k) A u then (1 : ℝ) else 0)
  let M := positiveShellConnectionMaximum G w r n
  have hc (e : G.edgeSet) : 0 ≤ c e := by
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
  have hk (k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
      θ * (1 - θ) ≤ ∑ e, (P k (ends₁ e) + P k (ends₂ e)) * c e := by
    exact positive_connection_osss_of_radius_shell G rank r hstep k B o (by omega)
      (fun b hb => (Finset.mem_Icc.mp hk).2.trans (hB b hb)) ends₁ ends₂ hends w hw U
  have hs := Finset.sum_le_sum (fun k hk' => hk k hk')
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  rw [Finset.sum_comm] at hs
  have hmax (u : V) : (∑ k ∈ Finset.Icc 1 n, P k u) ≤ M :=
    positiveShellConnectionSum_le_maximum G w r n u
  have hbound : (∑ e, ∑ k ∈ Finset.Icc 1 n, (P k (ends₁ e) + P k (ends₂ e)) * c e) ≤
      2 * M * ∑ e, c e := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    apply mul_le_mul_of_nonneg_right _ (hc e)
    linarith only [hmax (ends₁ e), hmax (ends₂ e)]
  exact hs.trans hbound

end
end PottsContinuity.BD12
