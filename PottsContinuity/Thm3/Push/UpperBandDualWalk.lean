module

public import PottsContinuity.Thm3.Push.UpperBandDualStep
public import PottsContinuity.Thm3.Push.WalkSupportStepPullback
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- A confined closed-dual walk whose bottom-row vertex is unique pulls back
to the band's true complementary dual. Unlike an induced-face restriction,
this transport cannot retain extra edges along the bottom port row. -/
theorem upper_band_closed_dual_walk_pullback (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H)
    (A : Configuration (rectangleGraph a w H))
    (u v : RectangleDualVertex (a.1,a.2+(t : ℤ)) w (H-t))
    (p : (openGraph (rectangleDualGraph a w H) (rectangleDualConfiguration a w H A)).Walk
      (rectangleDualVertexEmbedding (rectangle_dual_upper_band_subset a w H t ht) u)
      (rectangleDualVertexEmbedding (rectangle_dual_upper_band_subset a w H t ht) v))
    (hlo : ∀ z ∈ p.support, a.2+(t : ℤ)-1 ≤ z.val.2)
    (hbottom : ∀ x ∈ p.support, ∀ y ∈ p.support,
      x.val.2=a.2+(t : ℤ)-1 → y.val.2=a.2+(t : ℤ)-1 → x=y) :
    ∃ r : (openGraph (rectangleDualGraph (a.1,a.2+(t : ℤ)) w (H-t))
        (rectangleDualConfiguration (a.1,a.2+(t : ℤ)) w (H-t)
          (DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A))).Walk u v,
      ∀ x ∈ r.support,
        rectangleDualVertexEmbedding (rectangle_dual_upper_band_subset a w H t ht) x ∈ p.support := by
  let ι := rectangleDualVertexEmbedding (rectangle_dual_upper_band_subset a w H t ht)
  apply exists_walk_pullback_support_steps ι p u v rfl rfl
  · intro z hz
    have hprops := (mem_latticeRectangle (a.1-1,a.2-1) z.val (w+1) (H+1)).mp z.property
    have hzlo := hlo z hz
    have hsub : ((H-t : ℕ) : ℤ)=(H : ℤ)-(t : ℤ) := Nat.cast_sub ht
    have hmem : z.val ∈ rectangleDualExpanded (a.1,a.2+(t : ℤ)) w (H-t) := by
      rw [rectangleDualExpanded,mem_latticeRectangle]
      simp only [Nat.cast_add,Nat.cast_one] at hprops ⊢
      exact ⟨hprops.1,hzlo,by omega⟩
    exact ⟨⟨z.val,hmem⟩,Subtype.ext rfl⟩
  · intro x y hx hy hxy
    apply upper_band_closed_dual_step_pullback a w H t ht A x y hxy
    rintro ⟨hxb,hyb⟩
    exact hxy.ne (hbottom (ι x) hx (ι y) hy hxb hyb)

end
end PottsContinuity.Push
