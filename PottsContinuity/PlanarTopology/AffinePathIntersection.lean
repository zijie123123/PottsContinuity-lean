module

public import PottsContinuity.PD.Duality.RectanglePathIntersection
public import Mathlib.Topology.Path

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK.Curves unitInterval
noncomputable section

/-- If a clamped value lies strictly between the clamp bounds, the original
value equals it. -/
theorem clamp_eq_of_strict_interior {l r x y : ℝ} (hx : l < x ∧ x < r)
    (he : max l (min r y) = x) : y = x := by
  by_cases hy : y ≤ l
  · have hm : max l (min r y) = l := max_eq_left ((min_le_right _ _).trans hy)
    rw [hm] at he
    linarith
  · by_cases hy' : r ≤ y
    · have hm : max l (min r y) = r := by rw [min_eq_left hy',max_eq_right (by linarith)]
      rw [hm] at he
      linarith
    · simpa only [min_eq_right (le_of_not_ge hy'),max_eq_right (le_of_not_ge hy)] using he

/-- A path crossing a strict affine band horizontally meets every vertical
spanning path in the same horizontal slab. The spanning path may make
arbitrary excursions above and below the band. -/
theorem affine_paths_intersect {a b c d : ℂ} (P : Path a b) (Q : Path c d)
    (l r t β H : ℝ) (hlr : l ≤ r)
    (hP : ∀ s : I, l ≤ (P s).re ∧ (P s).re ≤ r ∧ |(P s).im-(t*(P s).re+β)| < H)
    (hQ : ∀ s : I, l ≤ (Q s).re ∧ (Q s).re ≤ r)
    (ha : a.re = l) (hb : b.re = r)
    (hc : c.im-(t*c.re+β) ≤ -H) (hd : H ≤ d.im-(t*d.re+β)) :
    ∃ s u : I, P s = Q u := by
  let shear : ℂ → ℝ × ℝ := fun z => (z.re,z.im-(t*z.re+β))
  let clip : ℂ → ℝ × ℝ := fun z => (z.re,max (-H) (min H (z.im-(t*z.re+β))))
  have hshear : Continuous shear := by dsimp [shear]; fun_prop
  have hclip : Continuous clip := by dsimp [clip]; fun_prop
  let P' := P.map hshear
  let Q' := Q.map hclip
  have hH : 0 < H := lt_of_le_of_lt (abs_nonneg _) (hP 0).2.2
  have hPbox : ∀ s : I, l ≤ (P' s).1 ∧ (P' s).1 ≤ r ∧ -H ≤ (P' s).2 ∧ (P' s).2 ≤ H := by
    intro s
    obtain ⟨hl,hr,hh⟩ := hP s
    exact ⟨hl,hr,(abs_lt.mp hh).1.le,(abs_lt.mp hh).2.le⟩
  have hQbox : ∀ s : I, l ≤ (Q' s).1 ∧ (Q' s).1 ≤ r ∧ -H ≤ (Q' s).2 ∧ (Q' s).2 ≤ H := by
    intro s
    refine ⟨(hQ s).1,(hQ s).2,le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
  have hleft : (P' 0).1 = l := by
    change (P 0).re = l
    rw [P.source,ha]
  have hright : (P' 1).1 = r := by
    change (P 1).re = r
    rw [P.target,hb]
  have hbottom : (Q' 0).2 = -H := by
    change max (-H) (min H ((Q 0).im-(t*(Q 0).re+β))) = -H
    rw [Q.source]
    exact max_eq_left ((min_le_right _ _).trans hc)
  have htop : (Q' 1).2 = H := by
    change max (-H) (min H ((Q 1).im-(t*(Q 1).re+β))) = H
    rw [Q.target,min_eq_left hd,max_eq_right (by linarith)]
  obtain ⟨s,u,hsu⟩ := pathRectangle_crossing_intersection
    (a := (l,-H)) (b := (r,H)) P' Q' hlr (by dsimp; linarith)
    hPbox hQbox hleft hright hbottom htop
  have hx : (P s).re = (Q u).re := congrArg Prod.fst hsu
  have hy : max (-H) (min H ((Q u).im-(t*(Q u).re+β))) =
      (P s).im-(t*(P s).re+β) := (congrArg Prod.snd hsu).symm
  have hy' := clamp_eq_of_strict_interior (abs_lt.mp (hP s).2.2) hy
  refine ⟨s,u,Complex.ext hx ?_⟩
  rw [hx] at hy'
  linarith

end
end PottsContinuity.PlanarTopology
