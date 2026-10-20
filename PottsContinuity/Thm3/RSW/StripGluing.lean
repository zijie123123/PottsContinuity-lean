module

public import PottsContinuity.Thm3.RSW.StripAssociation
public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# Finite gluing probabilities for the actual strip law

These lemmas perform only finite FKG multiplication and event inclusion. The
geometric gluing inclusion and the probabilities of the local connection events
are hypotheses here. In `Thm3.RSW.StripRSWFromThirteen` the inclusion is supplied by
`strip_translated_connections_glue_of_scale_le`, and in the proof of Lemma 2
(`Push.selfDual_stripRSW_of_directPrefixSystems`) the local bounds are supplied by
`Push.directPrefixSystem_rounded_local_of_small_horizontal`.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.RSW

/-- Finite positive association for clopen increasing events of the genuine
strip law, with no geometric or scale-dependent assumptions. -/
theorem strip_finite_fkg (θ : PD.FK.Parameters) (n : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    {ι : Type*} (s : Finset ι) (E : ι → Set (StripConfiguration n))
    (hclopen : ∀ j ∈ s, IsClopen (E j)) (hupper : ∀ j ∈ s, IsUpperSet (E j)) :
    (∏ j ∈ s, μ.real (E j)) ≤ μ.real (⋂ j ∈ s, E j) := by
  classical
  let : IsProbabilityMeasure μ := hμ.1
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
    have hsclopen : IsClopen (⋂ k ∈ s, E k) :=
      isClopen_biInter_finset fun k hk => hclopen k (Finset.mem_insert_of_mem hk)
    have hsupper : IsUpperSet (⋂ k ∈ s, E k) := by
      intro ω η h hω
      simp only [Set.mem_iInter] at hω ⊢
      intro k hk
      exact hupper k (Finset.mem_insert_of_mem hk) h (hω k hk)
    have hprod := ih
      (fun k hk => hclopen k (Finset.mem_insert_of_mem hk))
      (fun k hk => hupper k (Finset.mem_insert_of_mem hk))
    rw [Finset.prod_insert hjs]
    calc
      μ.real (E j) * ∏ k ∈ s, μ.real (E k) ≤
          μ.real (E j) * μ.real (⋂ k ∈ s, E k) :=
        mul_le_mul_of_nonneg_left hprod ENNReal.toReal_nonneg
      _ ≤ μ.real (E j ∩ ⋂ k ∈ s, E k) :=
        strip_clopen_fkg θ n μ hμ _ _ (hclopen j (Finset.mem_insert_self _ _))
          hsclopen (hupper j (Finset.mem_insert_self _ _)) hsupper
      _ = μ.real (⋂ k ∈ insert j s, E k) := by
        congr 1
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_insert]
        constructor
        · rintro ⟨hj, hs⟩ k (rfl | hk)
          · exact hj
          · exact hs k hk
        · intro h
          exact ⟨h j (Or.inl rfl), fun k hk => h k (Or.inr hk)⟩

/-- Uniform local connection-event bounds multiply under an explicit geometric
inclusion into the target event. The inclusion is a deterministic hypothesis,
not a stochastic RSW premise disguised as a boundary condition. -/
theorem strip_event_lower_of_finite_gluing (θ : PD.FK.Parameters) (n : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    {ι : Type*} (s : Finset ι) (E : ι → Set (StripConfiguration n))
    (H : Set (StripConfiguration n)) (b : ℝ) (hb : 0 ≤ b)
    (hclopen : ∀ j ∈ s, IsClopen (E j)) (hupper : ∀ j ∈ s, IsUpperSet (E j))
    (hlocal : ∀ j ∈ s, b ≤ μ.real (E j))
    (hglue : (⋂ j ∈ s, E j) ⊆ H) :
    b ^ s.card ≤ μ.real H := by
  let : IsProbabilityMeasure μ := hμ.1
  calc
    b ^ s.card = ∏ _j ∈ s, b := (Finset.prod_const b).symm
    _ ≤ ∏ j ∈ s, μ.real (E j) :=
      Finset.prod_le_prod₀ (fun _ _ => hb) hlocal
    _ ≤ μ.real (⋂ j ∈ s, E j) := strip_finite_fkg θ n μ hμ s E hclopen hupper
    _ ≤ μ.real H := measureReal_mono hglue

/-- Specialization to the actual self-dual strip crossing event. The finite
local-event bounds and gluing inclusion are left visible, rather than asserted
as a completed proof of Lemma 2. -/
theorem selfDual_strip_crossing_lower_of_finite_gluing
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (k : ℝ)
    {ι : Type*} (s : Finset ι) (E : ι → Set (StripConfiguration n))
    (b : ℝ) (hb : 0 ≤ b)
    (hclopen : ∀ j ∈ s, IsClopen (E j)) (hupper : ∀ j ∈ s, IsUpperSet (E j))
    (hlocal : ∀ j ∈ s, b ≤ (selfDualStripMeasure q n).real (E j))
    (hglue : (⋂ j ∈ s, E j) ⊆
      stripHorizontalCrossing n (-⌊k * n⌋) ⌊k * n⌋ 0 (2 * n)) :
    b ^ s.card ≤ selfDualStripHorizontalProbability q k n := by
  exact strip_event_lower_of_finite_gluing (selfDualParameters q) n
    (selfDualStripMeasure q n) (selfDualStripMeasure_isLimit q n)
    s E _ b hb hclopen hupper hlocal hglue

end PottsContinuity.RSW
