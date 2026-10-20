module

public import Mathlib
public import PottsContinuity.Frozen.Defs

/-!
# Uniqueness of the infinite-volume limit and of the critical point

Proofs of the two well-definedness statements that accompany the definitions of `Frozen/`
(`isRCInfiniteVolumeLimit_unique` and `isRCCriticalPoint_unique`): a probability measure on
`{0,1}^{E(ℤ²)}` is determined by its cylinder probabilities, so two infinite-volume limits
coincide (use the box exhaustion `Λₙ`); hence two critical points coincide (compare at the
midpoint).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity.WellDefined

open PottsContinuity

lemma box_monotone : Monotone (fun n : ℕ => box n) := by
  intro m n hmn x hx
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hx ⊢
  have : (m : ℤ) ≤ n := by exact_mod_cast hmn
  omega

lemma box_exhausts (x : ℤ × ℤ) : ∃ n, x ∈ box n := by
  refine ⟨max x.1.natAbs x.2.natAbs, ?_⟩
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  have h1 : x.1.natAbs ≤ max x.1.natAbs x.2.natAbs := le_max_left _ _
  have h2 : x.2.natAbs ≤ max x.1.natAbs x.2.natAbs := le_max_right _ _
  omega

/-- Two infinite-volume limits with the same parameters are equal. -/
theorem limit_unique (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (μ ν : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q i μ) (hν : IsRCInfiniteVolumeLimit p q i ν) : μ = ν := by
  classical
  have : IsProbabilityMeasure μ := hμ.1
  have : IsProbabilityMeasure ν := hν.1
  have hcyl : ∀ (A : Finset squareLattice.edgeSet) (ξ : squareLattice.edgeSet → Bool),
      μ {ω | ∀ e ∈ A, ω e = ξ e} = ν {ω | ∀ e ∈ A, ω e = ξ e} := by
    intro A ξ
    have h := tendsto_nhds_unique (hμ.2 _ box_monotone box_exhausts A ξ)
      (hν.2 _ box_monotone box_exhausts A ξ)
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h
  have hsing : ∀ (I : Finset squareLattice.edgeSet) (z : ∀ j : I, Bool),
      ν.map I.restrict {z} = μ.map I.restrict {z} := by
    intro I z
    rw [Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton z),
      Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton z)]
    have hset : (I.restrict ⁻¹' {z} : Set (squareLattice.edgeSet → Bool)) =
        {ω | ∀ e ∈ I, ω e = (fun e => if h : e ∈ I then z ⟨e, h⟩ else false) e} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h e he
        simp only [he, ↓reduceDIte, ← h]
        rfl
      · intro h
        funext j
        have := h j.1 j.2
        simpa [j.2] using this
    rw [hset]
    exact (hcyl I _).symm
  exact MeasureTheory.IsProjectiveLimit.unique (P := fun I => μ.map I.restrict)
    (fun I => rfl) (fun I => Measure.ext_of_singleton (hsing I))

/-- Two critical points for the same `q ≥ 1` are equal. -/
theorem criticalPoint_unique (q : Set.Ici (1 : ℝ)) (a b : ℝ)
    (ha : IsRCCriticalPoint q a) (hb : IsRCCriticalPoint q b) : a = b := by
  by_contra hne
  wlog hab : a < b generalizing a b
  · exact this b a hb ha (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hab) (Ne.symm hne))
  have hp : (a + b) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ha.1.1], by linarith [hb.1.2]⟩
  obtain ⟨μ, hμ, -, hpos⟩ := ha.2 ⟨(a + b) / 2, hp⟩
  obtain ⟨ν, hν, hzero, -⟩ := hb.2 ⟨(a + b) / 2, hp⟩
  obtain rfl := limit_unique _ _ 1 μ ν hμ hν
  have h1 := hpos (by show a < (a + b) / 2; linarith)
  rw [hzero (by show (a + b) / 2 < b; linarith)] at h1
  exact lt_irrefl _ h1

end PottsContinuity.WellDefined
