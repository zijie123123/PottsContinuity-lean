module

public import PottsContinuity.Thm3.Prop4.GoodCorridorCrossing
public import PottsContinuity.Thm3.Prop4.VerticalRectangleWiredError

/-!
# Quantitative bulk crossings of the actual sloped tube

The finite corridor is contained in the original Euclidean tube. A union
bound for its actual rectangle failures gives the error, using frozen
wired/free duality and the assumed stretched free-arm decay for every q.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- The complete concrete corridor fails with an explicit finite union error. -/
theorem selfDual_wired_corridor_failure_le (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 1 μ₁)
    (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hdecay : ∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ₀ m ≤ Real.exp (-c₀*(m : ℝ)^α))
    (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (ht : |t| ≤ 1) :
    μ₁.real (corridorGoodEvent n s hs t b)ᶜ ≤
      (10*(n : ℝ)+2)*(s : ℝ)*Real.exp (-c₀*((s : ℝ)+1)^α) := by
  classical
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  let E := Real.exp (-c₀*((s : ℝ)+1)^α)
  let H := fun i => BD12.horizontalRectangle
    (corridorAbscissa n s i,corridorCenter n s hs t b i-(s : ℤ)) (2*s) (2*s)
  let V := fun i => BD12.verticalRectangle
    (corridorAbscissa n s (i+1),min (corridorCenter n s hs t b i) (corridorCenter n s hs t b (i+1))-(s : ℤ))
    s (2*s+(corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i).natAbs)
  have hH : ∀ i, μ₁.real (H i)ᶜ ≤ 2*(s : ℝ)*E := by
    intro i
    have hb := selfDual_wired_rectangle_noncrossing_le_stretched q μ₀ μ₁ hμ₀ hμ₁
      c₀ α hc₀ hα hdecay
      (corridorAbscissa n s i,corridorCenter n s hs t b i-(s : ℤ)) (2*s) (2*s)
    have hpow : ((s : ℝ)+1)^α ≤ (2*(s : ℝ)+1)^α :=
      Real.rpow_le_rpow (by positivity)
        (by have h := Nat.cast_nonneg (α := ℝ) s; linarith only [h]) hα.le
    have he : Real.exp (-c₀*(2*(s : ℝ)+1)^α) ≤ E := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr hc₀.le)
    have hb' : μ₁.real (H i)ᶜ ≤ 2*(s : ℝ)*Real.exp (-c₀*(2*(s : ℝ)+1)^α) := by
      simpa only [H,Nat.cast_mul,Nat.cast_ofNat] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hV : ∀ i, μ₁.real (V i)ᶜ ≤ 3*(s : ℝ)*E := by
    intro i
    have hrow := corridorCenter_step n s hs t b ht i
    have hd : ((corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i).natAbs : ℤ) ≤ s := by
      simpa only [Int.natCast_natAbs] using hrow
    have hdR : ((corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i).natAbs : ℝ) ≤ s := by
      exact_mod_cast hd
    have hheight : ((2*s+(corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i).natAbs : ℕ) : ℝ) ≤ 3*(s : ℝ) := by
      push_cast
      linarith only [hdR]
    exact (selfDual_wired_vertical_rectangle_noncrossing_le_stretched q μ₀ μ₁ hμ₀ hμ₁
      c₀ α hc₀ hα hdecay _ s _).trans (mul_le_mul_of_nonneg_right hheight (Real.exp_nonneg _))
  have hcover : (corridorGoodEvent n s hs t b)ᶜ ⊆
      (⋃ i ∈ Finset.range (2*n+1), (H i)ᶜ) ∪ (⋃ i ∈ Finset.range (2*n), (V i)ᶜ) := by
    intro ω hω
    by_cases hh : ∀ i : ℕ, i < 2*n+1 → ω ∈ H i
    · have hv : ¬∀ i : ℕ, i < 2*n → ω ∈ V i := fun hv => hω ⟨hh,hv⟩
      push Not at hv
      obtain ⟨i,hi,hfail⟩ := hv
      exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hi,hfail⟩⟩)
    · push Not at hh
      obtain ⟨i,hi,hfail⟩ := hh
      exact Or.inl (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hi,hfail⟩⟩)
  calc
    _ ≤ μ₁.real ((⋃ i ∈ Finset.range (2*n+1), (H i)ᶜ) ∪ (⋃ i ∈ Finset.range (2*n), (V i)ᶜ)) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ₁.real (⋃ i ∈ Finset.range (2*n+1), (H i)ᶜ) + μ₁.real (⋃ i ∈ Finset.range (2*n), (V i)ᶜ) :=
      measureReal_union_le _ _
    _ ≤ (∑ i ∈ Finset.range (2*n+1), μ₁.real (H i)ᶜ) + (∑ i ∈ Finset.range (2*n), μ₁.real (V i)ᶜ) :=
      add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _)
    _ ≤ (∑ _i ∈ Finset.range (2*n+1), 2*(s : ℝ)*E) + (∑ _i ∈ Finset.range (2*n), 3*(s : ℝ)*E) :=
      add_le_add (Finset.sum_le_sum (fun i _ => hH i)) (Finset.sum_le_sum (fun i _ => hV i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      push_cast
      ring

/-- An actual sloped tube crossing has the same bulk error, with no planar escape interface. -/
theorem selfDual_wired_tube_noncrossing_le_corridor_error (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 1 μ₁)
    (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hdecay : ∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ₀ m ≤ Real.exp (-c₀*(m : ℝ)^α))
    {n : ℕ} (hn : 1 ≤ n) (s : ℕ) (hs : s ≤ n) (hspos : 1 ≤ s)
    (u v : LatticeVertex) (huB : u ∈ box n) (hvB : v ∈ box n)
    (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (R : ℝ) (hR : 4*(s : ℝ)+1 ≤ R) :
    μ₁.real (tubeHorizontalCrossingEvent n R u v)ᶜ ≤
      (10*(n : ℝ)+2)*(s : ℝ)*Real.exp (-c₀*((s : ℝ)+1)^α) := by
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  apply le_trans _ (selfDual_wired_corridor_failure_le q μ₀ μ₁ hμ₀ hμ₁ c₀ α hc₀ hα hdecay n s hs t b ht)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hfail hgood
  exact hfail (corridorGoodEvent_has_tube_crossing hn s hs hspos u v huB hvB ha hb t b ht hu hv R hR ω hgood)

end
end PottsContinuity.Thm3.Prop4
