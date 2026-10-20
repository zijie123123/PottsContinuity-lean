module

public import Mathlib
public import PottsContinuity.Thm1.FiniteESMagnetisation
public import PottsContinuity.Frozen.Defs

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open scoped ENNReal
open PottsContinuity

noncomputable section

private theorem eventually_subset_of_exhaustion
    (G : ℕ → Finset (ℤ × ℤ)) (hG : Monotone G)
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ G n) (A : Finset (ℤ × ℤ)) :
    ∀ᶠ n : ℕ in atTop, A ⊆ G n := by
  classical
  induction A using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall (fun _ => Finset.empty_subset _)
  | @insert a A ha ih =>
      obtain ⟨n, hn⟩ := hExhaust a
      filter_upwards [ih, Filter.eventually_ge_atTop n] with m hm hmn
      exact Finset.insert_subset (hG hmn hn) hm

/-- At zero inverse temperature, every finite cylinder matching probability is
the reciprocal power of the number of observed sites once those sites lie in V. -/
theorem pottsEventProb_zero_cylinder (q : ℕ) (i : Fin q)
    (V A : Finset (ℤ × ℤ)) (hA : A ⊆ V) (ξ : ℤ × ℤ → Fin q) :
    pottsEventProb V 0 i (fun σ => ∀ x ∈ A, σ x = ξ x) =
      ((q : ℝ)⁻¹) ^ A.card := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (by
    intro h
    subst q
    exact Fin.elim0 i)
  have hw : ∀ σ : V → Fin q, pottsProb V 0 i σ = ((q : ℝ) ^ V.card)⁻¹ := by
    intro σ
    unfold pottsProb pottsWeight
    simp only [zero_mul, Real.exp_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Nat.cast_pow, one_div]
  unfold pottsEventProb
  simp only [hw]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfilter :
      (Finset.univ.filter fun σ : V → Fin q =>
        ∀ x ∈ A, pottsExtend V i σ x = ξ x) =
      Fintype.piFinset (fun x : V =>
        if x.1 ∈ A then {ξ x.1} else Finset.univ) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x
      by_cases hx : x.1 ∈ A
      · simp [hx]
        simpa [pottsExtend, x.2] using h x.1 hx
      · simp [hx]
    · intro h x hx
      have hx' := h ⟨x, hA hx⟩
      simp [hx] at hx'
      simpa [pottsExtend, hA hx] using hx'
  rw [hfilter, Fintype.card_piFinset]
  have hprod :
      ∏ x : V, (if x.1 ∈ A then ({ξ x.1} : Finset (Fin q)) else Finset.univ).card =
        q ^ (V.card - A.card) := by
    have hpoint : ∀ x : V,
        (if x.1 ∈ A then ({ξ x.1} : Finset (Fin q)) else Finset.univ).card =
          (if x.1 ∈ A then 1 else q) := by
      intro x
      by_cases hx : x.1 ∈ A <;> simp [hx]
    simp only [hpoint]
    rw [Finset.univ_eq_attach, Finset.prod_attach V
      (fun y : ℤ × ℤ => if y ∈ A then 1 else q)]
    rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
    congr 1
    rw [Finset.filter_not, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hA, Finset.card_sdiff_of_subset hA]
  rw [hprod]
  have hle : A.card ≤ V.card := Finset.card_le_card hA
  have hpow :
      (q : ℝ) ^ V.card = (q : ℝ) ^ (V.card - A.card) * (q : ℝ) ^ A.card := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow]
  push_cast
  field_simp
  rw [one_div, ← mul_pow, mul_inv_cancel₀ (by exact_mod_cast hq.ne'), one_pow]

/-- The uniform product measure is the exact frozen Potts limit at zero
inverse temperature along every monotone exhaustive sequence. -/
theorem exists_isPottsInfiniteVolumeLimit_zero (q : ℕ) (i : Fin q) :
    ∃ μ : Measure (ℤ × ℤ → Fin q), IsPottsInfiniteVolumeLimit q 0 i μ := by
  classical
  let : Nonempty (Fin q) := ⟨i⟩
  let ρ : Measure (Fin q) := (PMF.uniformOfFintype (Fin q)).toMeasure
  let : IsProbabilityMeasure ρ := PMF.toMeasure.isProbabilityMeasure _
  refine ⟨Measure.infinitePi (fun _ : ℤ × ℤ => ρ), inferInstance, ?_⟩
  intro G hG hExhaust A ξ
  have hcyl :
      {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} =
        Set.pi (↑A) (fun x => {ξ x}) := by
    ext σ
    simp
  have hlimit :
      (Measure.infinitePi (fun _ : ℤ × ℤ => ρ)).real
        {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} =
        ((q : ℝ)⁻¹) ^ A.card := by
    rw [hcyl, Measure.real,
      Measure.infinitePi_pi _ (fun x _ => MeasurableSet.singleton _)]
    have hsingle : ∀ x : ℤ × ℤ, ρ {ξ x} = ((q : ℝ≥0∞))⁻¹ := by
      intro x
      simp [ρ, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
        PMF.uniformOfFintype_apply]
    simp only [hsingle, Finset.prod_const]
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [hlimit]
  have hsites := eventually_subset_of_exhaustion G hG hExhaust A
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hsites] with n hn
  exact (pottsEventProb_zero_cylinder q i (G n) A hn ξ).symm

end

end PottsContinuity.Thm1
