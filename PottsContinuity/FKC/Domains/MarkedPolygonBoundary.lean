-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/MarkedPolygonBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Schoenflies.PrePolygonArc
public import Schoenflies.Concatenate

/-!
# Two marked points on a polygonal boundary

A `PrePolygon` may contain collinear consecutive vertices. Its two complementary
forward arcs admit a simple closed parametrization with the marked vertices at
parameters `0` and `1 / 2`. The two closed half-intervals trace exactly those arcs.

The forward cyclic order here is the order of the supplied polygon's vertices.
No assertion identifies it with geometric counterclockwise orientation; that
identification needs a separate proof. No constant-speed condition is imposed.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set

private theorem concatenate_image_lowerHalf (f g : ℝ → Schoenflies.Plane) :
    Schoenflies.concatenate f g '' Icc (0 : ℝ) (1 / 2) = f '' (Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨2 * t, Schoenflies.double_mem_I ht,
      (Schoenflies.concatenate_of_le ht.2).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u / 2, ⟨by linarith only [hu.1], by linarith only [hu.2]⟩, ?_⟩
    rw [Schoenflies.concatenate_of_le (by linarith only [hu.2])]
    congr 1
    ring

private theorem concatenate_image_upperHalf (f g : ℝ → Schoenflies.Plane)
    (hmid : f 1 = g 0) :
    Schoenflies.concatenate f g '' Icc (1 / 2 : ℝ) 1 = g '' (Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨2 * t - 1, Schoenflies.doubleBack_mem_I ht,
      (Schoenflies.concatenate_upperHalf hmid ht).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(u + 1) / 2,
      ⟨by linarith only [hu.1], by linarith only [hu.2]⟩, ?_⟩
    rw [Schoenflies.concatenate_upperHalf hmid
      ⟨by linarith only [hu.1], by linarith only [hu.2]⟩]
    congr 1
    ring

/-- A polygon's two marked vertices can be placed at parameters zero and one-half,
while the two half-intervals follow its complementary forward arcs. This theorem
asserts the polygon's specified cyclic order, not geometric counterclockwise orientation. -/
theorem exists_marked_prePolygon_loop {m k : ℕ} (P : Schoenflies.PrePolygon m)
    (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    ∃ β : ℝ → Schoenflies.Plane, Schoenflies.IsLoop β ∧
      β 0 = P.vertex a ∧ β (1 / 2) = P.vertex (a + k) ∧ β 1 = P.vertex a ∧
      β '' (Icc (0 : ℝ) 1) = P.carrier ∧
      β '' Icc (0 : ℝ) (1 / 2) = P.arc a k ∧
      β '' Icc (1 / 2 : ℝ) 1 = P.arc (a + k) (m + 3 - k) := by
  have hwrap : a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le (show k ≤ m + 3 by omega),
      ZMod.natCast_self, add_zero]
  have hA := P.isArcBetween_arc a hk1 hk2
  have hB := P.isArcBetween_arc (a + k)
    (show 1 ≤ m + 3 - k by omega) (show m + 3 - k ≤ m + 2 by omega)
  rw [hwrap] at hB
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := hf1.trans hg0.symm
  have hclose : g 1 = f 0 := hg1.trans hf0.symm
  have hmeet : ∀ z ∈ f '' (Icc (0 : ℝ) 1), z ∈ g '' (Icc (0 : ℝ) 1) →
      z = f 0 ∨ z = f 1 := by
    intro z hzA hzB
    rw [hfim] at hzA
    rw [hgim] at hzB
    have hz : z ∈ ({P.vertex a, P.vertex (a + k)} : Set Schoenflies.Plane) :=
      P.arc_inter a hk1 hk2 ▸ ⟨hzA, hzB⟩
    simpa only [mem_insert_iff, mem_singleton_iff, hf0, hf1] using hz
  refine ⟨Schoenflies.concatenate f g,
    Schoenflies.IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Schoenflies.concatenate_zero, hf0]
  · rw [Schoenflies.concatenate_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)]
    norm_num only [mul_one_div, mul_one, div_self (show (2 : ℝ) ≠ 0 by norm_num)]
    exact hf1
  · rw [Schoenflies.concatenate_one, hg1]
  · rw [Schoenflies.image_concatenate hmid, hfim, hgim]
    exact P.arc_union a (by omega)
  · rw [concatenate_image_lowerHalf, hfim]
  · rw [concatenate_image_upperHalf f g hmid, hgim]

end PottsContinuity.FKC
