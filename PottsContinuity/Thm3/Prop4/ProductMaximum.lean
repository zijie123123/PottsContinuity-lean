module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Attainment of product suprema for zero-limit nonnegative sequences

DCST, TeX lines 1780–1791. The source writes maxima over infinite index
sets. The proof below supplies actual maximizers, including zero products,
for every nonempty constraint set of index pairs.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Every nonempty family of index pairs attains its maximum product when
both factors come from a nonnegative sequence tending to zero. -/
theorem exists_product_maximum (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hlim : Tendsto u atTop (𝓝 0)) (S : Set (ℕ × ℕ)) (hS : S.Nonempty) :
    ∃ p ∈ S, ∀ q ∈ S, u q.1*u q.2 ≤ u p.1*u p.2 := by
  classical
  obtain ⟨B,hB⟩ := hlim.bddAbove_range
  let M : ℝ := max B 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have huM : ∀ n, u n ≤ M := fun n => (hB (Set.mem_range_self n)).trans (le_max_left _ _)
  by_cases hpos : ∃ p ∈ S, 0 < u p.1*u p.2
  · obtain ⟨p,hp,hp0⟩ := hpos
    let v := u p.1*u p.2
    have hv : 0 < v/M := div_pos hp0 hM
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hv))
    let L := max N (max p.1 p.2)+1
    let F := ((Finset.range L).product (Finset.range L)).filter (fun q => q ∈ S)
    have hpF : p ∈ F := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
        Finset.mem_range.mpr ?_⟩, hp⟩ <;> dsimp [L] <;> omega
    obtain ⟨a,haF,hmax⟩ := Finset.exists_max_image F (fun q => u q.1*u q.2) ⟨p,hpF⟩
    have haS : a ∈ S := (Finset.mem_filter.mp haF).2
    have hpa : v ≤ u a.1*u a.2 := hmax p hpF
    refine ⟨a,haS,?_⟩
    intro q hq
    by_cases hqF : q.1 < L ∧ q.2 < L
    · exact hmax q (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hqF.1,Finset.mem_range.mpr hqF.2⟩,hq⟩)
    · by_cases hq1 : L ≤ q.1
      · have hsmall : u q.1 < v/M := hN q.1 (by dsimp [L] at hq1; omega)
        have hmul : u q.1*M < v := (lt_div_iff₀ hM).mp hsmall
        exact ((mul_le_mul_of_nonneg_left (huM q.2) (hu q.1)).trans hmul.le).trans hpa
      · have hq2 : L ≤ q.2 := by omega
        have hsmall : u q.2 < v/M := hN q.2 (by dsimp [L] at hq2; omega)
        have hmul : u q.2*M < v := (lt_div_iff₀ hM).mp hsmall
        have hprod : u q.1*u q.2 ≤ M*u q.2 := mul_le_mul_of_nonneg_right (huM q.1) (hu q.2)
        exact (hprod.trans (by simpa only [mul_comm] using hmul.le)).trans hpa
  · obtain ⟨p,hp⟩ := hS
    refine ⟨p,hp,?_⟩
    intro q hq
    have hq0 : u q.1*u q.2 ≤ 0 := by
      by_contra h
      exact hpos ⟨q,hq,lt_of_not_ge h⟩
    exact hq0.trans (mul_nonneg (hu p.1) (hu p.2))

end PottsContinuity.Thm3.Prop4
