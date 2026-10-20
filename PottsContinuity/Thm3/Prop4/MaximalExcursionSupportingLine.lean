module

public import PottsContinuity.Thm3.Prop4.LatticeCapsuleSupportingLine
public import PottsContinuity.Thm3.Prop4.TubeExcursion

/-!
# The original maximal Euclidean excursion has an admissible upper tangent

The source maximizing event is unchanged. Vertices outside the upper region
are either closer than the tube radius or below the original chord; both
cases lie below the capsule tangent already constructed at the maximum.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The entire finite trace lies below one admissible line through its
original maximal Euclidean upper-excursion vertex, without a parallelism premise. -/
theorem maximal_euclidean_excursion_below_admissible_line {Ω : Type*}
    {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (u v : ℤ × ℤ)
    (huB : u ∈ box n) (hvB : v ∈ box n) (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (trace : Ω → Finset (ℤ × ℤ)) (ω : Ω) (htrace : ∀ w ∈ trace ω, w ∈ box n)
    (z : ℤ × ℤ) (hz : ω ∈ maximalTubeExcursionEvent n ε u v trace z) :
    ∃ s c : ℝ, |s| ≤ 1 ∧ (z.2 : ℝ) = s*z.1+c ∧
      ∀ w ∈ trace ω, (w.2 : ℝ) ≤ s*w.1+c := by
  have hzData := Finset.mem_filter.mp hz.1
  have hrz : (n : ℝ)^ε ≤ tubeDistance u v z := by
    by_contra h
    exact hzData.2.1 ((mem_inductionTube n ε u v z).mpr ⟨hzData.1,lt_of_not_ge h⟩)
  obtain ⟨s,c,hs,hzc,hcap,hbelow⟩ := exists_upper_capsule_supporting_line hn u v z
    huB hvB huX hvX hzData.1 hzData.2.2
  refine ⟨s,c,hs,hzc,?_⟩
  intro w hw
  rcases inductionTube_three_region_cover hn ε u v huX hvX (htrace w hw) with hTube | hBelow | hAbove
  · exact hcap (tubeLatticePoint w) (((mem_inductionTube n ε u v w).mp hTube).2.le.trans hrz)
  · exact hbelow w (htrace w hw) (Finset.mem_filter.mp hBelow).2.2.le
  · exact hcap (tubeLatticePoint w) (hz.2.2 w hAbove hw)

end PottsContinuity.Thm3.Prop4
