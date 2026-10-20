module

public import PottsContinuity.Thm3.RSW.StripEvents

/-!
# Clipping a nearest-neighbour walk to a coordinate interval

A chain of intersecting paths may leave the horizontal target rectangle.
The lemma here supplies the separate clipping step while preserving any vertex
constraint, for example the vertical band containing the original paths.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- A walk spanning an integer coordinate interval contains a crossing confined
to that interval. Any original vertex constraint is retained. Only the no-jump
property of the coordinate along graph edges is used. -/
theorem walk_clip_coordinate {V : Type*} (G : SimpleGraph V) (f : V → ℤ)
    (hstep : ∀ {u v : V}, G.Adj u v → f v ≤ f u + 1)
    (a b : ℤ) (hab : a ≤ b) (P : V → Prop)
    {u v : V} (w : G.Walk u v) (hu : f u ≤ a) (hv : b ≤ f v)
    (hw : ∀ z ∈ w.support, P z) :
    ∃ (x y : V) (p : G.Walk x y),
      f x = a ∧ f y = b ∧ ∀ z ∈ p.support, a ≤ f z ∧ f z ≤ b ∧ P z := by
  classical
  suffices hmain : ∀ l : ℕ, ∀ {u v : V} (w : G.Walk u v), w.length = l →
      f u ≤ a → b ≤ f v → (∀ z ∈ w.support, P z) →
      ∃ (x y : V) (p : G.Walk x y),
        f x = a ∧ f y = b ∧ ∀ z ∈ p.support, a ≤ f z ∧ f z ≤ b ∧ P z from
    hmain w.length w rfl hu hv hw
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro u v w hlen hu hv hw
    by_cases hua : f u < a
    · cases w with
      | nil => simp only [SimpleGraph.Walk.length_nil] at hlen; omega
      | @cons u t v hut tail =>
        have ht : f t ≤ a := by have := hstep hut; omega
        apply ih tail.length (by simp only [SimpleGraph.Walk.length_cons] at hlen; omega)
          tail rfl ht hv
        intro z hz
        exact hw z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)
    have hua' : f u = a := by omega
    by_cases hvb : b < f v
    · cases hrev : w.reverse with
      | nil => omega
      | @cons v t u hvt tail =>
        have ht : b ≤ f t := by have := hstep (hvt.symm); omega
        have htlen : tail.length < l := by
          have he := congrArg SimpleGraph.Walk.length hrev
          simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons] at he
          omega
        apply ih tail.length htlen tail.reverse (by simp) hu ht
        intro z hz
        have hz' : z ∈ tail.support := by simpa only [SimpleGraph.Walk.support_reverse,
          List.mem_reverse] using hz
        have hzrev : z ∈ w.reverse.support := by
          rw [hrev]
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr hz'
        exact hw z (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzrev)
    have hvb' : f v = b := by omega
    by_cases hlow : ∃ z ∈ w.support, f z < a
    · obtain ⟨z, hz, hza⟩ := hlow
      have hzu : z ≠ u := by intro he; subst z; omega
      apply ih (w.dropUntil z hz).length (by
        rw [← hlen]
        exact SimpleGraph.Walk.length_dropUntil_lt_length hz hzu)
        (w.dropUntil z hz) rfl hza.le hv
      intro t ht
      exact hw t (w.support_dropUntil_subset_support hz ht)
    by_cases hhigh : ∃ z ∈ w.support, b < f z
    · obtain ⟨z, hz, hzb⟩ := hhigh
      have hzv : z ≠ v := by intro he; subst z; omega
      apply ih (w.takeUntil z hz).length (by
        rw [← hlen]
        exact SimpleGraph.Walk.length_takeUntil_lt_length hz hzv)
        (w.takeUntil z hz) rfl hu hzb.le
      intro t ht
      exact hw t (w.support_takeUntil_subset_support hz ht)
    refine ⟨u, v, w, hua', hvb', ?_⟩
    intro z hz
    exact ⟨by by_contra h; exact hlow ⟨z, hz, lt_of_not_ge h⟩,
      by by_contra h; exact hhigh ⟨z, hz, lt_of_not_ge h⟩, hw z hz⟩

/-- Every actual open strip edge is an original lattice edge. -/
theorem stripOpenGraph_le (n : ℕ) (ω : StripConfiguration n) :
    stripOpenGraph n ω ≤ stripGraph n := by
  rw [stripOpenGraph, SimpleGraph.fromEdgeSet_le]
  rintro e ⟨⟨he, _⟩, _⟩
  exact he

/-- Restricting the horizontal span of a rectangle preserves an actual crossing.
The proof clips the walk; it does not assume the original walk stays inside the
smaller horizontal interval. -/
theorem stripHorizontalCrossing_subset_of_horizontal_containment
    (n : ℕ) (a b c d a' b' : ℤ) (ha : a' ≤ a) (hab : a ≤ b) (hb : b ≤ b') :
    stripHorizontalCrossing n a' b' c d ⊆ stripHorizontalCrossing n a b c d := by
  rintro ω ⟨u, v, w, hu, hv, hw⟩
  have hstep : ∀ {u v : stripVertices n}, (stripOpenGraph n ω).Adj u v →
      v.1.1 ≤ u.1.1 + 1 := by
    intro u v huv
    have hsq := stripOpenGraph_le n ω huv
    change |u.1.1 - v.1.1| + |u.1.2 - v.1.2| = 1 at hsq
    have hnonneg := abs_nonneg (u.1.2 - v.1.2)
    have hdiff := neg_le_abs (u.1.1 - v.1.1)
    omega
  obtain ⟨x, y, p, hx, hy, hp⟩ := walk_clip_coordinate (stripOpenGraph n ω)
    (fun z => z.1.1) hstep a b hab (fun z => z.1.2 ∈ Set.Icc c d) w
    (by have := hu.1; simp only [Set.mem_singleton_iff] at this; omega)
    (by have := hv.1; simp only [Set.mem_singleton_iff] at this; omega)
    (fun z hz => (hw z hz).2)
  refine ⟨x, y, p, ⟨hx, (hp x p.start_mem_support).2.2⟩,
    ⟨hy, (hp y p.end_mem_support).2.2⟩, ?_⟩
  intro z hz
  exact ⟨⟨(hp z hz).1, (hp z hz).2.1⟩, (hp z hz).2.2⟩

/-- Self-dual strip crossing probabilities decrease with the nonnegative real
aspect ratio, with the original integer floor convention retained. -/
theorem selfDualStripHorizontalProbability_antitone (q : Set.Ici (1 : ℝ)) (n : ℕ)
    {k K : ℝ} (hk : 0 ≤ k) (hkK : k ≤ K) :
    selfDualStripHorizontalProbability q K n ≤ selfDualStripHorizontalProbability q k n := by
  apply MeasureTheory.measureReal_mono (h₂ := MeasureTheory.measure_ne_top _ _)
  apply stripHorizontalCrossing_subset_of_horizontal_containment
  · have := Int.floor_mono (mul_le_mul_of_nonneg_right hkK (Nat.cast_nonneg n))
    omega
  · have := Int.floor_nonneg.mpr (mul_nonneg hk (Nat.cast_nonneg n))
    omega
  · exact Int.floor_mono (mul_le_mul_of_nonneg_right hkK (Nat.cast_nonneg n))

end PottsContinuity.RSW
