module

public import PottsContinuity.BD12.SeparatingSeedRevealment
public import PottsContinuity.BD12.PositiveMean
public import PottsContinuity.BD12.FiniteOSSS
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! Positive-weight connection OSSS with the seed exploration's endpoint-connection
revealment estimates proved. No algorithm or revealment premise remains. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance positiveSeedOSSSEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveSeedOSSSEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
variable [MeasurableSpace (PD.FK.Configuration G)] [MeasurableSingletonClass (PD.FK.Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- The positive-weight connection variance is bounded by endpoint-to-seed
probabilities times edge covariances. The only geometric hypothesis is the
structural separator of original graph walks. -/
theorem positive_connection_osss_of_separator
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (S B : Finset V) (o : V)
    (hsep : ∀ b, b ∈ B → ∀ p : G.Walk o b, ∃ s, s ∈ p.support ∧ s ∈ S)
    (ends₁ ends₂ : G.edgeSet → V) (hends : ∀ e, e.val = s(ends₁ e, ends₂ e))
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (hw : ∀ A D, (w A : ℝ) * w D ≤ (w (A ∩ D) : ℝ) * w (A ∪ D)) (U : ℕ → ℝ) :
    let f := finiteConnectionToSetIndicator G o B
    let θ := finitePositiveMean w f
    θ * (1 - θ) ≤ ∑ e,
      (finitePositiveMean w (fun A => if FKC.FiniteFK.actualMultiClusterConnected G S A (ends₁ e) then 1 else 0) +
        finitePositiveMean w (fun A => if FKC.FiniteFK.actualMultiClusterConnected G S A (ends₂ e) then 1 else 0)) *
      finitePositiveCovariance w f (fun A => if e ∈ A then 1 else 0) := by
  let f := finiteConnectionToSetIndicator G o B
  let T := seedClusterRevealTree G rank S ∅ ∅
  let c := fun e => finitePositiveCovariance w f (fun A => if e ∈ A then (1 : ℝ) else 0)
  have hf := finiteConnectionToSetIndicator_monotone G o B
  have hf01 := finiteConnectionToSetIndicator_mem_Icc G o B
  have hc (e : G.edgeSet) : 0 ≤ c e := by
    let I := fun A : PD.FK.Configuration G => if e ∈ A then (1 : ℝ) else 0
    have hI0 : ∀ A, 0 ≤ I A := by intro A; dsimp [I]; split_ifs <;> norm_num
    have hIm : Monotone I := by
      intro A D hAD
      dsimp only [I]
      by_cases hA : e ∈ A
      · simp only [ite_eq_left hA, ite_eq_left (hAD hA), le_refl]
      · simp only [ite_eq_right hA]; split_ifs <;> norm_num
    exact finitePositiveCovariance_nonneg w hw f I (fun A => (hf01 A).1) hI0 hf hIm
  have hsq : (fun A => f A ^ 2) = f := by
    funext A
    dsimp only [f, finiteConnectionToSetIndicator]
    split_ifs <;> norm_num
  have hOSSS := finite_osss_monotone w hw f hf hf01 U (fun _ => 0) T
  rw [hsq] at hOSSS
  have hbound (e : G.edgeSet) := finiteConnection_seed_revealment_le_of_separator
    G rank S B o hsep w U e (ends₁ e) (ends₂ e) (hends e)
  have hsum := Finset.sum_le_sum (fun e (_he : e ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hbound e) (hc e))
  have h := hOSSS.trans hsum
  dsimp only
  convert h using 1; ring

/-- Radius shells supply the separator literally by integer intermediate
values along walks. Every probability and covariance is the actual positive finite law. -/
theorem positive_connection_osss_of_radius_shell [Fintype V]
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet))
    (r : V → ℕ) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    (k : ℕ) (B : Finset V) (o : V) (ho : r o ≤ k) (hB : ∀ b ∈ B, k ≤ r b)
    (ends₁ ends₂ : G.edgeSet → V) (hends : ∀ e, e.val = s(ends₁ e, ends₂ e))
    (w : PD.FK.Configuration G → Set.Ioi (0 : ℝ))
    (hw : ∀ A D, (w A : ℝ) * w D ≤ (w (A ∩ D) : ℝ) * w (A ∪ D)) (U : ℕ → ℝ) :
    let S := finiteRadiusShell r k
    let f := finiteConnectionToSetIndicator G o B
    let θ := finitePositiveMean w f
    θ * (1 - θ) ≤ ∑ e,
      (finitePositiveMean w (fun A => if FKC.FiniteFK.actualMultiClusterConnected G S A (ends₁ e) then 1 else 0) +
        finitePositiveMean w (fun A => if FKC.FiniteFK.actualMultiClusterConnected G S A (ends₂ e) then 1 else 0)) *
      finitePositiveCovariance w f (fun A => if e ∈ A then 1 else 0) := by
  apply positive_connection_osss_of_separator G rank (finiteRadiusShell r k) B o _ ends₁ ends₂ hends w hw U
  intro b hb p
  exact walk_visits_finiteRadiusShell r hstep p k ho (hB b hb)

end
end PottsContinuity.BD12
