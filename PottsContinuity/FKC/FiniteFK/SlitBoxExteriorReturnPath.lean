-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxExteriorReturnPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

def slitReturnVerticalUpWalk (x y : ℤ) : (d : ℕ) →
    squareLattice.Walk (x, y) (x, y + (d : ℤ))
  | 0 => (SimpleGraph.Walk.nil : squareLattice.Walk (x, y) (x, y)).copy (by simp) (by simp)
  | d + 1 => by
      have h : squareLattice.Adj (x, y) (x, y + 1) := by
        rw [squareLattice_adj_iff]
        exact Or.inr ⟨rfl, Or.inl rfl⟩
      exact (SimpleGraph.Walk.cons h (slitReturnVerticalUpWalk x (y + 1) d)).copy
        (by simp) (by push_cast; ring_nf)

def slitReturnHorizontalRightWalk (x y : ℤ) : (d : ℕ) →
    squareLattice.Walk (x, y) (x + (d : ℤ), y)
  | 0 => (SimpleGraph.Walk.nil : squareLattice.Walk (x, y) (x, y)).copy (by simp) (by simp)
  | d + 1 => by
      have h : squareLattice.Adj (x, y) (x + 1, y) := by
        rw [squareLattice_adj_iff]
        exact Or.inl ⟨Or.inl rfl, rfl⟩
      exact (SimpleGraph.Walk.cons h (slitReturnHorizontalRightWalk (x + 1) y d)).copy
        (by simp) (by push_cast; ring_nf)

theorem slitReturnVerticalUpWalk_support_bounds (x y : ℤ) (d : ℕ) {z : LatticeVertex}
    (hz : z ∈ (slitReturnVerticalUpWalk x y d).support) :
    z.1 = x ∧ y ≤ z.2 ∧ z.2 ≤ y + (d : ℤ) := by
  induction d generalizing y z with
  | zero =>
      simp [slitReturnVerticalUpWalk] at hz
      rcases hz with rfl
      simp
  | succ d ih =>
      simp only [slitReturnVerticalUpWalk, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨rfl, le_rfl, by omega⟩
      · obtain ⟨hx, hlo, hhi⟩ := ih (y + 1) hz
        refine ⟨hx, ?_, ?_⟩ <;> omega

theorem slitReturnHorizontalRightWalk_support_bounds (x y : ℤ) (d : ℕ)
    {z : LatticeVertex} (hz : z ∈ (slitReturnHorizontalRightWalk x y d).support) :
    z.2 = y ∧ x ≤ z.1 ∧ z.1 ≤ x + (d : ℤ) := by
  induction d generalizing x z with
  | zero =>
      simp [slitReturnHorizontalRightWalk] at hz
      rcases hz with rfl
      simp
  | succ d ih =>
      simp only [slitReturnHorizontalRightWalk, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨rfl, le_rfl, by omega⟩
      · obtain ⟨hy, hlo, hhi⟩ := ih (x + 1) hz
        refine ⟨hy, ?_, ?_⟩ <;> omega

theorem slitReturnVerticalUpWalk_isPath (x y : ℤ) (d : ℕ) :
    (slitReturnVerticalUpWalk x y d).IsPath := by
  induction d generalizing y with
  | zero => simp [slitReturnVerticalUpWalk]
  | succ d ih =>
      rw [SimpleGraph.Walk.isPath_def]
      simp only [slitReturnVerticalUpWalk, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨_, hlo, _⟩ := slitReturnVerticalUpWalk_support_bounds x (y + 1) d hmem
        omega
      · exact (ih (y + 1)).support_nodup

theorem slitReturnHorizontalRightWalk_isPath (x y : ℤ) (d : ℕ) :
    (slitReturnHorizontalRightWalk x y d).IsPath := by
  induction d generalizing x with
  | zero => simp [slitReturnHorizontalRightWalk]
  | succ d ih =>
      rw [SimpleGraph.Walk.isPath_def]
      simp only [slitReturnHorizontalRightWalk, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨_, hlo, _⟩ := slitReturnHorizontalRightWalk_support_bounds (x + 1) y d hmem
        omega
      · exact (ih (x + 1)).support_nodup

/-- An explicit exterior return walk from an arc vertex to a bottom point.
Its ordered route follows the top, right, and bottom exterior corridors. -/
def slitBoxExteriorReturnWalkNat (n a k : ℕ) (ha : a ≤ n) (hk : k ≤ n) :
    {p : squareLattice.Walk ((0 : ℤ), (k : ℤ)) ((a : ℤ), -(n : ℤ)) //
      ((n + 1 : ℤ), (n + 1 : ℤ)) ∈ p.support} := by
  let p1 : squareLattice.Walk ((0 : ℤ), (k : ℤ))
      ((0 : ℤ), (n + 1 : ℤ)) := by
    have h := slitReturnVerticalUpWalk 0 (k : ℤ) (n + 1 - k)
    have heq : (k : ℤ) + ((n + 1 - k : ℕ) : ℤ) = (n + 1 : ℤ) := by
      have hkn : k ≤ n + 1 := by omega
      rw [Nat.cast_sub hkn]
      push_cast
      omega
    exact h.copy (by simp) (by rw [heq])
  let p2 : squareLattice.Walk ((0 : ℤ), (n + 1 : ℤ))
      ((n + 1 : ℤ), (n + 1 : ℤ)) := by
    exact (slitReturnHorizontalRightWalk 0 (n + 1 : ℤ) (n + 1)).copy
      (by simp) (by simp)
  let p3 : squareLattice.Walk ((n + 1 : ℤ), (n + 1 : ℤ))
      ((n + 1 : ℤ), -(n + 1 : ℤ)) := by
    let p := slitReturnVerticalUpWalk (n + 1 : ℤ) (-(n + 1 : ℤ)) (2 * (n + 1))
    have heq : -(n + 1 : ℤ) + ((2 * (n + 1) : ℕ) : ℤ) = (n + 1 : ℤ) := by
      push_cast
      omega
    have p' : squareLattice.Walk ((n + 1 : ℤ), -(n + 1 : ℤ))
        ((n + 1 : ℤ), (n + 1 : ℤ)) := p.copy (by simp) (by rw [heq])
    exact p'.reverse
  let p4 : squareLattice.Walk ((n + 1 : ℤ), -(n + 1 : ℤ))
      ((a : ℤ), -(n + 1 : ℤ)) := by
    let p := slitReturnHorizontalRightWalk (a : ℤ) (-(n + 1 : ℤ)) (n + 1 - a)
    have heq : (a : ℤ) + ((n + 1 - a : ℕ) : ℤ) = (n + 1 : ℤ) := by
      have han : a ≤ n + 1 := by omega
      rw [Nat.cast_sub han]
      push_cast
      omega
    have p' : squareLattice.Walk ((a : ℤ), -(n + 1 : ℤ))
        ((n + 1 : ℤ), -(n + 1 : ℤ)) := p.copy (by simp) (by rw [heq])
    exact p'.reverse
  let p5 : squareLattice.Walk ((a : ℤ), -(n + 1 : ℤ))
      ((a : ℤ), -(n : ℤ)) := by
    exact (slitReturnVerticalUpWalk (a : ℤ) (-(n + 1 : ℤ)) 1).copy
      (by simp) (by simp)
  let rest := p3.append (p4.append p5)
  let tail := p2.append rest
  let route := p1.append tail
  have hcornerTail : ((n + 1 : ℤ), (n + 1 : ℤ)) ∈ tail.support := by
    exact SimpleGraph.Walk.support_subset_support_append_left p2 rest
      p2.end_mem_support
  have hcorner : ((n + 1 : ℤ), (n + 1 : ℤ)) ∈ route.support :=
    SimpleGraph.Walk.support_subset_support_append_right p1 tail hcornerTail
  exact ⟨route, hcorner⟩

/-- Any point of the explicit route that lies in the `2n` square is either
the terminal bottom point or belongs to the retained vertical arc. -/
theorem slitBoxExteriorReturnWalkNat_support_in_box
    (n a k : ℕ) (ha : a ≤ n) (hk : k ≤ n) {z : LatticeVertex}
    (hz : z ∈ (slitBoxExteriorReturnWalkNat n a k ha hk).val.support)
    (hzBox : z ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)) :
    z = ((a : ℤ), -(n : ℤ)) ∨
      (z.1 = 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ (n : ℤ)) := by
  rw [mem_latticeRectangle] at hzBox
  have hright : z.1 ≤ (n : ℤ) := by
    have := hzBox.1.2
    have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
      push_cast
      omega
    omega
  have htop : z.2 ≤ (n : ℤ) := by
    have := hzBox.2.2
    have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
      push_cast
      omega
    omega
  unfold slitBoxExteriorReturnWalkNat at hz
  dsimp only at hz
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz1 | hzrest
  · obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds 0 (k : ℤ)
      (n + 1 - k) (by simpa only [SimpleGraph.Walk.support_copy] using hz1)
    right
    refine ⟨hx, ?_, htop⟩
    omega
  · rcases hzrest with hz2 | hzrest
    · obtain ⟨hy, hlo, hhi⟩ := slitReturnHorizontalRightWalk_support_bounds 0
        (n + 1 : ℤ) (n + 1) (by simpa [SimpleGraph.Walk.support_copy] using hz2)
      omega
    · rcases hzrest with hz3 | hzrest
      · obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
          (n + 1 : ℤ) (-(n + 1 : ℤ)) (2 * (n + 1)) (by
            simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz3)
        omega
      · rcases hzrest with hz4 | hz5
        · obtain ⟨hy, hlo, hhi⟩ := slitReturnHorizontalRightWalk_support_bounds
            (a : ℤ) (-(n + 1 : ℤ)) (n + 1 - a) (by
              simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz4)
          omega
        · obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
            (a : ℤ) (-(n + 1 : ℤ)) 1 (by
              simpa [SimpleGraph.Walk.support_copy] using hz5)
          left
          apply Prod.ext <;> omega

end PottsContinuity.FKC.FiniteFK
