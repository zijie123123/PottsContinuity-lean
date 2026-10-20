module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Tactic

/-! Contiguous extraction from the given walk, without loop erasure or rerouting. -/

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Split a walk at a set vertex. Every other prefix vertex is outside the set. -/
theorem walk_first_entry {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (B : Set V) (hv : v ∈ B) :
    ∃ z ∈ B, ∃ (r : G.Walk u z) (s : G.Walk z v),
      p = r.append s ∧ ∀ x ∈ r.support, x ∈ B → x = z := by
  classical
  induction p with
  | @nil u =>
    exact ⟨u, hv, .nil, .nil, rfl, by simp⟩
  | @cons u w v h p ih =>
    by_cases hu : u ∈ B
    · exact ⟨u, hu, .nil, p.cons h, rfl, by simp⟩
    · obtain ⟨z, hz, r, s, heq, hr⟩ := ih hv
      refine ⟨z, hz, r.cons h, s, ?_, ?_⟩
      · rw [heq]
        rfl
      · intro x hx hxB
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hu hxB).elim
        · exact hr x hx hxB

/-- A unit-step integer-valued coordinate attains every intermediate level in a prefix.
All vertices of the selected prefix lie at or below the terminal level. -/
theorem walk_prefix_at_level {V : Type*} {G : SimpleGraph V}
    (f : V → ℤ) (hstep : ∀ x y, G.Adj x y → |f x - f y| ≤ 1)
    {u v : V} (p : G.Walk u v) (b : ℤ) (hu : f u ≤ b) (hv : b ≤ f v) :
    ∃ z, ∃ (r : G.Walk u z) (s : G.Walk z v),
      f z = b ∧ p = r.append s ∧ ∀ x ∈ r.support, f x ≤ b := by
  induction p with
  | @nil u =>
    exact ⟨u, .nil, .nil, le_antisymm hu hv, rfl, by simpa using hu⟩
  | @cons u w v h p ih =>
    by_cases hub : f u = b
    · exact ⟨u, .nil, p.cons h, hub, rfl, by simpa using hu⟩
    · have hw : f w ≤ b := by
        have hs := (abs_le.mp (hstep u w h)).1
        omega
      obtain ⟨z, r, s, hz, heq, hr⟩ := ih hw hv
      refine ⟨z, r.cons h, s, hz, ?_, ?_⟩
      · rw [heq]
        rfl
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hu
        · exact hr x hx

/-- Between an initial coordinate below `a` and a final coordinate above `b`, extract
an actual contiguous `a`-to-`b` subwalk staying within the slab `[a,b]`. -/
theorem walk_subwalk_between_levels {V : Type*} {G : SimpleGraph V}
    (f : V → ℤ) (hstep : ∀ x y, G.Adj x y → |f x - f y| ≤ 1)
    {u v : V} (p : G.Walk u v) {a b : ℤ}
    (hab : a ≤ b) (hu : f u ≤ a) (hv : b ≤ f v) :
    ∃ x y, ∃ r : G.Walk x y, r.IsSubwalk p ∧
      f x = a ∧ f y = b ∧ ∀ z ∈ r.support, a ≤ f z ∧ f z ≤ b := by
  obtain ⟨y, t, s, hy, hp, ht⟩ :=
    walk_prefix_at_level f hstep p b (hu.trans hab) hv
  have hneg : ∀ x y, G.Adj x y → |(-f x) - (-f y)| ≤ 1 := by
    intro x y h
    simpa only [neg_sub_neg, abs_sub_comm] using hstep x y h
  obtain ⟨x, r, k, hx, htr, hr⟩ := walk_prefix_at_level
    (fun z => -f z) hneg t.reverse (-a) (by omega) (by omega)
  have ht' : t = k.reverse.append r.reverse := by
    have he := congrArg SimpleGraph.Walk.reverse htr
    simpa only [SimpleGraph.Walk.reverse_reverse, SimpleGraph.Walk.reverse_append] using he
  have hrt : r.reverse.IsSubwalk t :=
    SimpleGraph.Walk.isSubwalk_of_append_right ht'
  have hrp : r.reverse.IsSubwalk p :=
    hrt.trans (SimpleGraph.Walk.isSubwalk_of_append_left hp)
  refine ⟨x, y, r.reverse, hrp, by omega, hy, ?_⟩
  intro z hz
  have hzr : z ∈ r.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  exact ⟨by have := hr z hzr; omega, ht z (hrt.support_subset hz)⟩

/-- The extracted slab crossing is simple whenever the original walk is simple. -/
theorem path_subpath_between_levels {V : Type*} {G : SimpleGraph V}
    (f : V → ℤ) (hstep : ∀ x y, G.Adj x y → |f x - f y| ≤ 1)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) {a b : ℤ}
    (hab : a ≤ b) (hu : f u ≤ a) (hv : b ≤ f v) :
    ∃ x y, ∃ r : G.Walk x y, r.IsSubwalk p ∧ r.IsPath ∧
      f x = a ∧ f y = b ∧ ∀ z ∈ r.support, a ≤ f z ∧ f z ≤ b := by
  obtain ⟨x, y, r, hr, hx, hy, hb⟩ := walk_subwalk_between_levels f hstep p hab hu hv
  exact ⟨x, y, r, hr, SimpleGraph.Walk.isPath_of_isSubwalk hr hp, hx, hy, hb⟩

end PottsContinuity.PlanarTopology
