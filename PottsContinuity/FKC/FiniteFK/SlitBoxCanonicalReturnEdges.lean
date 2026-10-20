-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCanonicalReturnEdges.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- Every vertical unit bond in a vertical-up recursive walk occurs in its
actual edge list. -/
theorem slitReturnVerticalUpWalk_edge_mem (x y : ℤ) (d : ℕ) (j : ℤ)
    (hlo : y ≤ j) (hhi : j < y + (d : ℤ)) :
    s((x, j), (x, j + 1)) ∈ (slitReturnVerticalUpWalk x y d).edges := by
  induction d generalizing y j with
  | zero => omega
  | succ d ih =>
      by_cases hfirst : j = y
      · subst j
        simp only [slitReturnVerticalUpWalk, SimpleGraph.Walk.edges_copy,
          SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl trivial
      · have hlo' : y + 1 ≤ j := by omega
        have hhi' : j < (y + 1) + (d : ℤ) := by omega
        have hrec := ih (y + 1) j hlo' hhi'
        simp only [slitReturnVerticalUpWalk, SimpleGraph.Walk.edges_copy,
          SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr hrec

/-- Every horizontal unit bond in a horizontal-right recursive walk occurs in
its actual edge list. -/
theorem slitReturnHorizontalRightWalk_edge_mem (x y : ℤ) (d : ℕ) (j : ℤ)
    (hlo : x ≤ j) (hhi : j < x + (d : ℤ)) :
    s((j, y), (j + 1, y)) ∈ (slitReturnHorizontalRightWalk x y d).edges := by
  induction d generalizing x j with
  | zero => omega
  | succ d ih =>
      by_cases hfirst : j = x
      · subst j
        simp only [slitReturnHorizontalRightWalk, SimpleGraph.Walk.edges_copy,
          SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl trivial
      · have hlo' : x + 1 ≤ j := by omega
        have hhi' : j < (x + 1) + (d : ℤ) := by omega
        have hrec := ih (x + 1) j hlo' hhi'
        simp only [slitReturnHorizontalRightWalk, SimpleGraph.Walk.edges_copy,
          SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr hrec

/-- The canonical five-piece exterior return route contains each vertical
right-side bond in its full range. -/
theorem slitBoxExteriorReturnWalkNat_right_edge_mem
    (n a k : ℕ) (ha : a ≤ n) (hk : k ≤ n) (j : ℤ)
    (hlo : -(n + 1 : ℤ) ≤ j) (hhi : j ≤ (n : ℤ)) :
    s(((n + 1 : ℤ), j), ((n + 1 : ℤ), j + 1)) ∈
      (slitBoxExteriorReturnWalkNat n a k ha hk).val.edges := by
  have hp3 := slitReturnVerticalUpWalk_edge_mem (n + 1 : ℤ) (-(n + 1 : ℤ))
    (2 * (n + 1)) j (by omega) (by omega)
  simp only [slitBoxExteriorReturnWalkNat, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_append, List.mem_append,
    SimpleGraph.Walk.edges_reverse, List.mem_reverse] at *
  aesop

/-- The canonical five-piece exterior return route contains each top bond. -/
theorem slitBoxExteriorReturnWalkNat_top_edge_mem
    (n a k : ℕ) (ha : a ≤ n) (hk : k ≤ n) (j : ℤ)
    (hlo : 0 ≤ j) (hhi : j ≤ (n : ℤ)) :
    s((j, (n + 1 : ℤ)), (j + 1, (n + 1 : ℤ))) ∈
      (slitBoxExteriorReturnWalkNat n a k ha hk).val.edges := by
  have hp2 := slitReturnHorizontalRightWalk_edge_mem (0 : ℤ) (n + 1 : ℤ)
    (n + 1) j (by omega) (by omega)
  simp only [slitBoxExteriorReturnWalkNat, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_append, List.mem_append] at *
  aesop

private theorem canonicalReturn_horizontal_bound
    (n : ℕ) (u : SlitBoxVertex n) (huX : 0 ≤ u.val.1) :
    u.val.1.toNat ≤ n := by
  have huBox := u.property
  rw [mem_latticeRectangle] at huBox
  have hx := huBox.1.2
  have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
    push_cast
    omega
  rw [hmax] at hx
  have hxInt : (u.val.1.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg huX]
    exact hx
  exact_mod_cast hxInt

private theorem canonicalReturn_vertical_bound
    (n : ℕ) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    t.val.2.toNat ≤ n := by
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  have htInt : (t.val.2.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg htArc.2.1]
    exact htArc.2.2
  exact_mod_cast htInt

/-- The endpoint-copied canonical return walk retains every right-side unit
bond from its lower to upper corner. -/
theorem slitBoxCanonicalReturnWalk_right_edge_mem
    (n : ℕ) (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ))
    (huX : 0 ≤ u.val.1) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    (j : ℤ) (hlo : -(n + 1 : ℤ) ≤ j) (hhi : j ≤ (n : ℤ)) :
    s(((n + 1 : ℤ), j), ((n + 1 : ℤ), j + 1)) ∈
      (slitBoxCanonicalReturnWalk n u huY huX t ht).edges := by
  have h := slitBoxExteriorReturnWalkNat_right_edge_mem n u.val.1.toNat
    t.val.2.toNat (canonicalReturn_horizontal_bound n u huX)
    (canonicalReturn_vertical_bound n t ht) j hlo hhi
  simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.edges_copy] using h

/-- The endpoint-copied canonical return walk retains every top unit bond. -/
theorem slitBoxCanonicalReturnWalk_top_edge_mem
    (n : ℕ) (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ))
    (huX : 0 ≤ u.val.1) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    (j : ℤ) (hlo : 0 ≤ j) (hhi : j ≤ (n : ℤ)) :
    s((j, (n + 1 : ℤ)), (j + 1, (n + 1 : ℤ))) ∈
      (slitBoxCanonicalReturnWalk n u huY huX t ht).edges := by
  have h := slitBoxExteriorReturnWalkNat_top_edge_mem n u.val.1.toNat
    t.val.2.toNat (canonicalReturn_horizontal_bound n u huX)
    (canonicalReturn_vertical_bound n t ht) j hlo hhi
  simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.edges_copy] using h

end PottsContinuity.FKC.FiniteFK
