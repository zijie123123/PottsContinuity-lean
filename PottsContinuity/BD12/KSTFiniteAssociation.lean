module

public import PottsContinuity.BD12.KSTProbability

/-! Finite FKG products for KST construction and finite-cover gluing. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] [Preorder Ω] [Fintype ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (hFKG : ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    IsUpperSet A → IsUpperSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))

include hFKG

theorem kst_finite_intersection_lower (S : ι → Set Ω)
    (hS : ∀ i, MeasurableSet (S i)) (hSu : ∀ i, IsUpperSet (S i)) (s : Finset ι) :
    (∏ i ∈ s, μ.real (S i)) ≤ μ.real (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have heq : (⋂ i ∈ insert a s, S i) = S a ∩ (⋂ i ∈ s, S i) := by
      ext ω
      simp
    rw [Finset.prod_insert ha, heq]
    exact (mul_le_mul_of_nonneg_left ih (measureReal_nonneg)).trans
      (hFKG _ _ (hS a) (MeasurableSet.iInter fun i =>
        MeasurableSet.iInter fun _ : i ∈ s => hS i)
        (hSu a) (isUpperSet_iInter₂ fun i _ => hSu i))

/-- The finite square-root-trick inequality before taking an N-th root. -/
theorem kst_finite_union_upper (S : ι → Set Ω)
    (hS : ∀ i, MeasurableSet (S i)) (hSu : ∀ i, IsUpperSet (S i)) (s : Finset ι) :
    μ.real (⋃ i ∈ s, S i) ≤ 1 - ∏ i ∈ s, (1 - μ.real (S i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have heq : (⋃ i ∈ insert a s, S i) = S a ∪ (⋃ i ∈ s, S i) := by
      ext ω
      simp
    rw [Finset.prod_insert ha, heq]
    have hu := kst_union_bound μ hFKG (hS a)
      (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ : i ∈ s => hS i)
      (hSu a) (isUpperSet_iUnion₂ fun i _ => hSu i)
    have ha1 : μ.real (S a) ≤ 1 := measureReal_le_one
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1)
      (sub_nonneg.mpr ih)]

/-- Any finite deterministic gluing construction inherits the FKG product
bound; in particular this handles the six events constructing Q(4m,m). -/
theorem kst_construction_of_kstCorridor (S : ι → Set Ω)
    (hS : ∀ i, MeasurableSet (S i)) (hSu : ∀ i, IsUpperSet (S i))
    {Q : Set Ω} (hconstruction : (⋂ i, S i) ⊆ Q) :
    (∏ i, μ.real (S i)) ≤ μ.real Q := by
  have h := kst_finite_intersection_lower μ hFKG S hS hSu Finset.univ
  simp only [Finset.mem_univ, Set.iInter_true] at h
  exact h.trans (measureReal_mono hconstruction)

/-- The construction product is at least the N-th power of any common lower
bound on the input probabilities. -/
theorem kst_construction_uniform_of_kstCorridor (S : ι → Set Ω)
    (hS : ∀ i, MeasurableSet (S i)) (hSu : ∀ i, IsUpperSet (S i))
    {Q : Set Ω} (hconstruction : (⋂ i, S i) ⊆ Q)
    (a : ℝ) (ha : 0 ≤ a) (hbound : ∀ i, a ≤ μ.real (S i)) :
    a ^ Fintype.card ι ≤ μ.real Q := by
  have hp : (∏ _i : ι, a) ≤ ∏ i, μ.real (S i) :=
    Finset.prod_le_prod₀ (fun _ _ => ha) (fun i _ => hbound i)
  simpa only [Finset.prod_const, Finset.card_univ] using
    hp.trans (kst_construction_of_kstCorridor μ hFKG S hS hSu hconstruction)

/-- A finite cover supplies a large-probability constituent in the precise
polynomial form of the square-root trick, with no loss at probability one. -/
theorem kst_finite_cover_square_root [Nonempty ι] (S : ι → Set Ω)
    (hS : ∀ i, MeasurableSet (S i)) (hSu : ∀ i, IsUpperSet (S i))
    {B : Set Ω} (hcover : B ⊆ ⋃ i, S i) :
    ∃ i, (1 - μ.real (S i)) ^ Fintype.card ι ≤ 1 - μ.real B := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => μ.real (S j)) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have hp : (∏ _j : ι, (1 - μ.real (S i))) ≤ ∏ j, (1 - μ.real (S j)) := by
    apply Finset.prod_le_prod₀
    · intro _ _
      exact sub_nonneg.mpr measureReal_le_one
    · intro j _
      exact sub_le_sub_left (hmax j (Finset.mem_univ j)) 1
  have hu := kst_finite_union_upper μ hFKG S hS hSu Finset.univ
  simp only [Finset.mem_univ, Set.iUnion_true] at hu
  have hb := measureReal_mono (μ := μ) hcover
  simp only [Finset.prod_const, Finset.card_univ] at hp
  linarith

end PottsContinuity.BD12
