module

public import PottsContinuity.Thm1.FiniteESNonneg
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import PottsContinuity.Frozen.Defs

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance pottsESFiniteSpinVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESFiniteSpinEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESFiniteSpinConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

def pottsESFiniteSpinDistribution (V : Finset (ℤ × ℤ)) (q : ℕ)
    (hq : 1 ≤ q) (β : ℝ) (hβ : 0 ≤ β) (i : Fin q) : PMF (V → Fin q) :=
  (pottsESJointLawNonneg V q hq β hβ i).map Prod.fst

theorem pottsESFiniteSpinDistribution_apply (V : Finset (ℤ × ℤ)) (q : ℕ)
    (hq : 1 ≤ q) (β : ℝ) (hβ : 0 ≤ β) (i : Fin q) (σ : V → Fin q) :
    pottsESFiniteSpinDistribution V q hq β hβ i σ =
      ENNReal.ofReal (pottsProb V β i σ) := by
  classical
  let : Nonempty (V → Fin q) := ⟨fun _ => i⟩
  calc
    pottsESFiniteSpinDistribution V q hq β hβ i σ =
        ∑ ω : (pottsESGraph V).edgeSet → Bool,
          pottsESJointLawNonneg V q hq β hβ i (σ, ω) := by
      rw [pottsESFiniteSpinDistribution, PMF.map_apply, tsum_fintype,
        Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Fintype.sum_eq_single σ (by
        intro x hne
        have hEq : ¬ σ = (x, ω).1 := by
          intro h
          apply hne
          simpa using h.symm
        simp [hEq])]
      simp
    _ = ∑ ω : (pottsESGraph V).edgeSet → Bool,
          ENNReal.ofReal
            (esJointProbability β (pottsESEdgeAgreement V i) σ ω) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [pottsESJointLawNonneg_apply]
    _ = ENNReal.ofReal
        (∑ ω : (pottsESGraph V).edgeSet → Bool,
          esJointProbability β (pottsESEdgeAgreement V i) σ ω) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro ω hω
      exact esJointProbability_nonneg hβ (pottsESEdgeAgreement V i) σ ω
    _ = ENNReal.ofReal (pottsProb V β i σ) := by
      congr 1
      exact esJointProbability_spin_marginal_potts V β i σ

lemma pottsESFiniteSpinExtension_measurable (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) : Measurable (pottsExtend V i) := by
  apply measurable_pi_iff.mpr
  intro x
  by_cases hx : x ∈ V
  · simpa [pottsExtend, hx] using
      (measurable_pi_apply (⟨x, hx⟩ : V))
  · simp [pottsExtend, hx]

def pottsESFiniteSpinProbabilityMeasure (V : Finset (ℤ × ℤ)) (q : ℕ)
    (hq : 1 ≤ q) (β : ℝ) (hβ : 0 ≤ β) (i : Fin q) :
    ProbabilityMeasure (ℤ × ℤ → Fin q) := by
  let p := pottsESFiniteSpinDistribution V q hq β hβ i
  exact ⟨((p.map (pottsExtend V i)).toMeasure), PMF.toMeasure.isProbabilityMeasure _⟩

lemma pottsESSpinCylinder_measurable (q : ℕ) (A : Finset (ℤ × ℤ))
    (ξ : ℤ × ℤ → Fin q) :
    MeasurableSet {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} := by
  rw [show {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} =
    ⋂ x ∈ A, {σ : ℤ × ℤ → Fin q | σ x = ξ x} by ext σ; simp]
  exact A.measurableSet_biInter fun x hx => by
    change MeasurableSet
      ((fun σ : ℤ × ℤ → Fin q => σ x) ⁻¹' ({ξ x} : Set (Fin q)))
    exact measurable_pi_apply x (measurableSet_singleton (ξ x))

theorem pottsESFiniteSpinProbabilityMeasure_cylinder
    (V A : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (β : ℝ) (hβ : 0 ≤ β) (i : Fin q) (ξ : ℤ × ℤ → Fin q) :
    (pottsESFiniteSpinProbabilityMeasure V q hq β hβ i :
      Measure (ℤ × ℤ → Fin q)).real
        {σ | ∀ x ∈ A, σ x = ξ x} =
      pottsEventProb V β i (fun σ => ∀ x ∈ A, σ x = ξ x) := by
  classical
  let p := pottsESFiniteSpinDistribution V q hq β hβ i
  have hEvent : MeasurableSet {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} :=
    pottsESSpinCylinder_measurable q A ξ
  rw [Measure.real,
    show (pottsESFiniteSpinProbabilityMeasure V q hq β hβ i :
        Measure (ℤ × ℤ → Fin q)) = (p.map (pottsExtend V i)).toMeasure by rfl,
    PMF.toMeasure_map_apply (pottsExtend V i) p _
      (pottsESFiniteSpinExtension_measurable V i) hEvent]
  have hpre :
      pottsExtend V i ⁻¹' {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} =
        {σ : V → Fin q | ∀ x ∈ A, pottsExtend V i σ x = ξ x} := rfl
  rw [hpre, PMF.toMeasure_apply_fintype]
  have hprobNonneg (σ : V → Fin q) : 0 ≤ pottsProb V β i σ := by
    have hweight (τ : V → Fin q) : 0 < pottsWeight V β i τ := by
      unfold pottsWeight
      exact Real.exp_pos _
    have hZ : 0 < ∑ τ : V → Fin q, pottsWeight V β i τ := by
      apply Finset.sum_pos
      · intro τ hτ
        exact hweight τ
      · exact ⟨fun _ => i, Finset.mem_univ _⟩
    unfold pottsProb
    exact div_nonneg (hweight σ).le hZ.le
  have hToReal : ENNReal.toReal
      (∑ σ : V → Fin q,
        {σ : V → Fin q | ∀ x ∈ A, pottsExtend V i σ x = ξ x}.indicator p σ) =
      ∑ σ : V → Fin q,
        if (∀ x ∈ A, pottsExtend V i σ x = ξ x) then pottsProb V β i σ else 0 := by
    rw [show (∑ σ : V → Fin q,
        {σ : V → Fin q | ∀ x ∈ A, pottsExtend V i σ x = ξ x}.indicator p σ) =
      ∑ σ ∈ (Finset.univ : Finset (V → Fin q)),
        {σ : V → Fin q | ∀ x ∈ A, pottsExtend V i σ x = ξ x}.indicator p σ by simp]
    rw [ENNReal.toReal_sum (s := Finset.univ)
      (f := fun σ : V → Fin q =>
        {σ : V → Fin q | ∀ x ∈ A, pottsExtend V i σ x = ξ x}.indicator p σ)
      (by
        intro σ hσ
        rw [Set.indicator_apply]
        change (if ∀ x ∈ A, pottsExtend V i σ x = ξ x then
          p σ else 0) ≠ ⊤
        split_ifs
        · exact p.apply_ne_top σ
        · exact ENNReal.zero_ne_top)]
    apply Finset.sum_congr rfl
    intro σ hσ
    have hterm : ENNReal.toReal
        ({σ : V → Fin q | ∀ x ∈ A, pottsExtend V i σ x = ξ x}.indicator p σ) =
        if (∀ x ∈ A, pottsExtend V i σ x = ξ x) then
          pottsProb V β i σ else 0 := by
      rw [Set.indicator_apply]
      by_cases hs : ∀ x ∈ A, pottsExtend V i σ x = ξ x
      · have hmem : σ ∈ {σ : V → Fin q |
            ∀ x ∈ A, pottsExtend V i σ x = ξ x} := hs
        rw [ite_eq_left hmem, ite_eq_left hs]
        change ENNReal.toReal (pottsESFiniteSpinDistribution V q hq β hβ i σ) =
          pottsProb V β i σ
        rw [pottsESFiniteSpinDistribution_apply]
        exact ENNReal.toReal_ofReal (hprobNonneg σ)
      · have hmem : σ ∉ {σ : V → Fin q |
            ∀ x ∈ A, pottsExtend V i σ x = ξ x} := hs
        rw [ite_eq_right hmem, ite_eq_right hs]
        rfl
    exact hterm
  simpa [pottsEventProb, Set.indicator_apply] using hToReal

end

end PottsContinuity.Thm1
