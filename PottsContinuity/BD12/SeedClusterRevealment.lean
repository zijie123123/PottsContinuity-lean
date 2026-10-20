module

public import PottsContinuity.BD12.SeedClusterQuerySupport
public import PottsContinuity.BD12.OriginalEvalMoments
public import PottsContinuity.BD12.FiniteOSSS
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! The actual boundary-seed exploration revealment is bounded by endpoint
connection probabilities under the original positive-weight law. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory FKC.FiniteFK
open scoped Classical
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance seedRevealEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedRevealEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
variable [MeasurableSpace (Configuration G)] [MeasurableSingletonClass (Configuration G)]
    [MeasurableSpace (Option G.edgeSet)] [MeasurableSingletonClass (Option G.edgeSet)]

/-- Actual algorithmic revealment is at most the original-law probability
that the edge touches an actual seed cluster. No exploration premise remains. -/
theorem seedClusterRevealTree_revealment_le
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (S B : Finset V) (o : V)
    (w : Configuration G → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ) (e : G.edgeSet) :
    finiteRevealment w (seedMediatedIndicator G S B o) U (seedClusterRevealTree G rank S ∅ ∅) e ≤
      finitePinnedMean w ∅ ∅ (fun A => if e ∈ actualMultiClusterReveal G S A then 1 else 0) := by
  classical
  let T := seedClusterRevealTree G rank S ∅ ∅
  let μ := finiteOriginalPinBlock 0 (Fintype.card G.edgeSet) U
  let D := {W | ∃ t ∈ Finset.range (Fintype.card G.edgeSet),
    finiteActiveOriginalQueryAt w (seedMediatedIndicator G S B o) W t T ∅ = some e}
  let g := fun A : Configuration G => if e ∈ actualMultiClusterReveal G S A then (1 : ℝ) else 0
  have hD : MeasurableSet D := by
    simp only [D, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro t
    by_cases ht : t ∈ Finset.range (Fintype.card G.edgeSet)
    · simpa only [ht, true_and] using
        finiteActiveOriginalQueryAt_fibre_measurableSet w (seedMediatedIndicator G S B o) t T ∅ e
    · simp only [ht, false_and, Set.ofPred_false]
      exact MeasurableSet.empty
  have hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1 := by intro A; dsimp [g]; split_ifs <;> norm_num
  have hX : Measurable (fun W => g (finiteOriginalEval w W T ∅)) :=
    (measurable_of_finite g).comp (finiteOriginalEval_measurable w T ∅)
  have hi := integrable_of_unit_bounds μ hX (fun W => hg01 _)
  have hpoint (W : ℕ → ℝ) : D.indicator (fun _ => (1 : ℝ)) W ≤ g (finiteOriginalEval w W T ∅) := by
    by_cases hW : W ∈ D
    · rw [Set.indicator_of_mem hW]
      obtain ⟨t, _, ht⟩ := hW
      have hmem := seedClusterRevealTree_active_query_support G rank S B o w W t ∅ ∅ e ht
      change e ∈ actualMultiClusterReveal G S (finiteOriginalEval w W T ∅) at hmem
      simp only [g, ite_eq_left hmem, le_refl]
    · simp only [Set.indicator_of_notMem hW]
      exact (hg01 _).1
  have h := integral_mono ((integrable_const (1 : ℝ)).indicator hD) hi hpoint
  rw [integral_indicator_const (1 : ℝ) hD, smul_eq_mul, mul_one,
    finiteOriginalEval_block_integral w g hg01 U T] at h
  exact h

/-- DRT's endpoint-connection revealment bound for the concrete constructed
tree, valid for every positive weight law (no FKG needed for this estimate). -/
theorem seedClusterRevealTree_revealment_le_endpoints
    (rank : G.edgeSet ≃ Fin (Fintype.card G.edgeSet)) (S B : Finset V) (o : V)
    (w : Configuration G → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ)
    (e : G.edgeSet) (u v : V) (he : e.val = s(u,v)) :
    finiteRevealment w (seedMediatedIndicator G S B o) U (seedClusterRevealTree G rank S ∅ ∅) e ≤
      finitePinnedMean w ∅ ∅ (fun A => if actualMultiClusterConnected G S A u then 1 else 0) +
      finitePinnedMean w ∅ ∅ (fun A => if actualMultiClusterConnected G S A v then 1 else 0) := by
  classical
  apply (seedClusterRevealTree_revealment_le G rank S B o w U e).trans
  have hmem (A : Configuration G) : e ∈ actualMultiClusterReveal G S A ↔
      actualMultiClusterConnected G S A u ∨ actualMultiClusterConnected G S A v := by
    rw [actualMultiClusterReveal_mem_iff]
    constructor
    · rintro ⟨z, hz, s, hs, hsz⟩
      rw [he] at hz
      rcases (Sym2.mem_iff').mp hz with hzu | hzv
      · exact Or.inl ⟨s, hs, hzu ▸ hsz⟩
      · exact Or.inr ⟨s, hs, hzv ▸ hsz⟩
    · rintro (⟨s, hs, hsu⟩ | ⟨s, hs, hsv⟩)
      · exact ⟨u, he.symm ▸ (Sym2.mem_iff').mpr (Or.inl rfl), s, hs, hsu⟩
      · exact ⟨v, he.symm ▸ (Sym2.mem_iff').mpr (Or.inr rfl), s, hs, hsv⟩
  simp_rw [finitePinnedMean_eq_sum_law]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro A _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  simp only [hmem A]
  by_cases hu : actualMultiClusterConnected G S A u <;>
    by_cases hv : actualMultiClusterConnected G S A v <;> simp [hu, hv]

end
end PottsContinuity.BD12
