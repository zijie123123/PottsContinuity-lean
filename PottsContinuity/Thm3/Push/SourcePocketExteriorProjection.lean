module

public import PottsContinuity.Thm3.Push.PocketAugmentedSourceReveal

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Projection preserves pocket augmentation, including the components
that avoid both seed sets. -/
theorem source_pocketAugmentedCutExterior_iff
    (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) (cut : Set (RectangleVertex (0,0) w h))
    (left right : Set (Vertex M x)) (u : RectangleVertex (0,0) w h) :
    Sum.inl u ∈ pocketAugmentedCutExterior (sourceExteriorGraph w h x y)
      (Sum.inl '' cut) (exteriorProjection M x w h '' left)
      (exteriorProjection M x w h '' right) ↔
    rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u ∈
      pocketAugmentedCutExterior (graph M x y)
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) '' cut)
        left right := by
  unfold pocketAugmentedCutExterior
  simp only [Set.mem_union,Set.mem_compl_iff,← Set.image_union]
  rw [source_closedCutExterior_iff M x y w h hM hx hxw hleft hright hh hyh cut right u,
    source_closedCutExterior_iff M x y w h hM hx hxw hleft hright hh hyh cut (left ∪ right) u]

/-- The augmented left source exterior is the exact clipped reference set. -/
theorem pocketAugmentedSourceLeftExterior_iff
    (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) (cut : Set (RectangleVertex (0,0) w h))
    (u : RectangleVertex (0,0) w h) :
    u ∈ pocketAugmentedSourceLeftExterior w h x y cut ↔
    rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u ∈
      pocketAugmentedCutExterior (graph M x y)
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) '' cut)
        (beta M x y) (alpha M x) := by
  have hc := source_pocketAugmentedCutExterior_iff M x y w h hM hx hxw hleft hright hh hyh
    cut (beta M x y) (alpha M x) u
  rw [exteriorProjection_image_alpha M x w h hM hx hxw hleft hright hh,
    exteriorProjection_image_beta M x y w h hM hx hxw hleft hright hh] at hc
  exact hc

/-- The augmented right source exterior is the exact clipped reference set. -/
theorem pocketAugmentedSourceRightExterior_iff
    (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) (cut : Set (RectangleVertex (0,0) w h))
    (u : RectangleVertex (0,0) w h) :
    u ∈ pocketAugmentedSourceRightExterior w h x y cut ↔
    rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u ∈
      pocketAugmentedCutExterior (graph M x y)
        (rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) '' cut)
        (alpha M x) (beta M x y) := by
  have hc := source_pocketAugmentedCutExterior_iff M x y w h hM hx hxw hleft hright hh hyh
    cut (alpha M x) (beta M x y) u
  rw [exteriorProjection_image_alpha M x w h hM hx hxw hleft hright hh,
    exteriorProjection_image_beta M x y w h hM hx hxw hleft hright hh] at hc
  exact hc

end
end PottsContinuity.Push
