-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxExteriorReturnSimple.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxExteriorReturnPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

private theorem slitReturn_append_isPath
    {u v w : LatticeVertex} {p : squareLattice.Walk u v}
    {q : squareLattice.Walk v w} (hp : p.IsPath) (hq : q.IsPath)
    (hdis : p.support.Disjoint q.support.tail) : (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append']
  exact ⟨hp.support_nodup, hq.support_nodup.tail, hdis⟩

private theorem slitReturn_support_nodup_start_not_tail
    {u v : LatticeVertex} {p : squareLattice.Walk u v}
    (hp : p.IsPath) : u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← SimpleGraph.Walk.cons_tail_support] at h
  exact (List.nodup_cons.mp h).1

/-- The literal five-segment exterior return route is simple whenever its
box scale is positive. -/
theorem slitBoxExteriorReturnWalkNat_isPath
    (n a k : ℕ) (hn : 1 ≤ n) (ha : a ≤ n) (hk : k ≤ n) :
    (slitBoxExteriorReturnWalkNat n a k ha hk).val.IsPath := by
  classical
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
      ((n + 1 : ℤ), (n + 1 : ℤ)) :=
    (slitReturnHorizontalRightWalk 0 (n + 1 : ℤ) (n + 1)).copy
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
      ((a : ℤ), -(n : ℤ)) :=
    (slitReturnVerticalUpWalk (a : ℤ) (-(n + 1 : ℤ)) 1).copy
      (by simp) (by simp)
  have hroute :
      (slitBoxExteriorReturnWalkNat n a k ha hk).val =
        p1.append (p2.append (p3.append (p4.append p5))) := by
    rfl
  have hp1 : p1.IsPath := by
    dsimp [p1]
    exact (SimpleGraph.Walk.isPath_copy _ _ _).2
      (slitReturnVerticalUpWalk_isPath _ _ _)
  have hp2 : p2.IsPath := by
    dsimp [p2]
    exact (SimpleGraph.Walk.isPath_copy _ _ _).2
      (slitReturnHorizontalRightWalk_isPath _ _ _)
  have hp3 : p3.IsPath := by
    dsimp [p3]
    exact ((SimpleGraph.Walk.isPath_copy _ _ _).2
      (slitReturnVerticalUpWalk_isPath _ _ _)).reverse
  have hp4 : p4.IsPath := by
    dsimp [p4]
    exact ((SimpleGraph.Walk.isPath_copy _ _ _).2
      (slitReturnHorizontalRightWalk_isPath _ _ _)).reverse
  have hp5 : p5.IsPath := by
    dsimp [p5]
    exact (SimpleGraph.Walk.isPath_copy _ _ _).2
      (slitReturnVerticalUpWalk_isPath _ _ _)
  have hrange1 (z : LatticeVertex) (hz : z ∈ p1.support) :
      z.1 = 0 ∧ (k : ℤ) ≤ z.2 ∧ z.2 ≤ (n + 1 : ℤ) := by
    dsimp [p1] at hz
    obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
      0 (k : ℤ) (n + 1 - k) (by simpa [SimpleGraph.Walk.support_copy] using hz)
    have hsum : (k : ℤ) + ((n + 1 - k : ℕ) : ℤ) = (n + 1 : ℤ) := by
      rw [Nat.cast_sub (by omega : k ≤ n + 1)]
      push_cast
      omega
    exact ⟨hx, hlo, by rw [hsum] at hhi; exact hhi⟩
  have hrange2 (z : LatticeVertex) (hz : z ∈ p2.support) :
      z.2 = (n + 1 : ℤ) ∧ 0 ≤ z.1 ∧ z.1 ≤ (n + 1 : ℤ) := by
    dsimp [p2] at hz
    obtain ⟨hy, hlo, hhi⟩ := slitReturnHorizontalRightWalk_support_bounds
      0 (n + 1 : ℤ) (n + 1) (by simpa [SimpleGraph.Walk.support_copy] using hz)
    exact ⟨hy, hlo, by push_cast at hhi ⊢; omega⟩
  have hrange3 (z : LatticeVertex) (hz : z ∈ p3.support) :
      z.1 = (n + 1 : ℤ) ∧ -(n + 1 : ℤ) ≤ z.2 ∧ z.2 ≤ (n + 1 : ℤ) := by
    dsimp [p3] at hz
    obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds
      (n + 1 : ℤ) (-(n + 1 : ℤ)) (2 * (n + 1)) (by
        simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz)
    have hsum : -(n + 1 : ℤ) + ((2 * (n + 1) : ℕ) : ℤ) = (n + 1 : ℤ) := by
      push_cast
      omega
    exact ⟨hx, hlo, by rw [hsum] at hhi; exact hhi⟩
  have hrange4 (z : LatticeVertex) (hz : z ∈ p4.support) :
      z.2 = -(n + 1 : ℤ) ∧ (a : ℤ) ≤ z.1 ∧ z.1 ≤ (n + 1 : ℤ) := by
    dsimp [p4] at hz
    obtain ⟨hy, hlo, hhi⟩ := slitReturnHorizontalRightWalk_support_bounds
      (a : ℤ) (-(n + 1 : ℤ)) (n + 1 - a) (by
        simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using hz)
    have hsum : (a : ℤ) + ((n + 1 - a : ℕ) : ℤ) = (n + 1 : ℤ) := by
      rw [Nat.cast_sub (by omega : a ≤ n + 1)]
      push_cast
      omega
    exact ⟨hy, hlo, by rw [hsum] at hhi; exact hhi⟩
  have hp5tail : p5.support.tail = [((a : ℤ), -(n : ℤ))] := by
    dsimp [p5]
    simp only [SimpleGraph.Walk.support_copy]
    simp [slitReturnVerticalUpWalk]
  have hroutePath : (p1.append (p2.append (p3.append (p4.append p5)))).IsPath := by
    have hp45 := slitReturn_append_isPath hp4 hp5 (by
      apply List.disjoint_left.mpr
      intro z hz4 hz5
      rw [hp5tail] at hz5
      simp only [List.mem_singleton] at hz5
      subst z
      have h4 := hrange4 _ hz4
      omega)
    have hp345 := slitReturn_append_isPath hp3 hp45 (by
      apply List.disjoint_left.mpr
      intro z hz3 hz45
      rw [SimpleGraph.Walk.tail_support_append] at hz45
      simp only [List.mem_append] at hz45
      rcases hz45 with hz4 | hz5
      · have h3 := hrange3 _ hz3
        have h4 := hrange4 _ (List.mem_of_mem_tail hz4)
        have hstart : z = ((n + 1 : ℤ), -(n + 1 : ℤ)) := by
          apply Prod.ext <;> omega
        have hnot := slitReturn_support_nodup_start_not_tail hp4
        exact hnot (by simpa [hstart] using hz4)
      · rw [hp5tail] at hz5
        simp only [List.mem_singleton] at hz5
        subst z
        have h3 := hrange3 _ hz3
        have haBound : (a : ℤ) ≤ (n : ℤ) := by exact_mod_cast ha
        omega)
    have hp2345 := slitReturn_append_isPath hp2 hp345 (by
      apply List.disjoint_left.mpr
      intro z hz2 hz345
      rw [SimpleGraph.Walk.tail_support_append] at hz345
      simp only [List.mem_append] at hz345
      rcases hz345 with hz3 | hz45
      · have h2 := hrange2 _ hz2
        have h3 := hrange3 _ (List.mem_of_mem_tail hz3)
        have hstart : z = ((n + 1 : ℤ), (n + 1 : ℤ)) := by
          apply Prod.ext <;> omega
        have hnot := slitReturn_support_nodup_start_not_tail hp3
        exact hnot (by
          have : z ∈ p3.support.tail := hz3
          simpa [hstart] using this)
      · rw [SimpleGraph.Walk.tail_support_append] at hz45
        simp only [List.mem_append] at hz45
        rcases hz45 with hz4 | hz5
        · have h2 := hrange2 _ hz2
          have h4 := hrange4 _ (List.mem_of_mem_tail hz4)
          omega
        · rw [hp5tail] at hz5
          simp only [List.mem_singleton] at hz5
          subst z
          have h2 := hrange2 _ hz2
          omega)
    have hrouteBuilt := slitReturn_append_isPath hp1 hp2345 (by
      apply List.disjoint_left.mpr
      intro z hz1 hz2345
      rw [SimpleGraph.Walk.tail_support_append] at hz2345
      simp only [List.mem_append] at hz2345
      rcases hz2345 with hz2 | hz345
      · have h1 := hrange1 _ hz1
        have h2 := hrange2 _ (List.mem_of_mem_tail hz2)
        have hstart : z = ((0 : ℤ), (n + 1 : ℤ)) := by
          apply Prod.ext <;> omega
        have hnot := slitReturn_support_nodup_start_not_tail hp2
        exact hnot (by
          have : z ∈ p2.support.tail := hz2
          simpa [hstart] using this)
      · rw [SimpleGraph.Walk.tail_support_append] at hz345
        simp only [List.mem_append] at hz345
        rcases hz345 with hz3 | hz45
        · have h1 := hrange1 _ hz1
          have h3 := hrange3 _ (List.mem_of_mem_tail hz3)
          omega
        · rw [SimpleGraph.Walk.tail_support_append] at hz45
          simp only [List.mem_append] at hz45
          rcases hz45 with hz4 | hz5
          · have h1 := hrange1 _ hz1
            have h4 := hrange4 _ (List.mem_of_mem_tail hz4)
            have hnpos : 0 < (n : ℤ) := by exact_mod_cast hn
            omega
          · rw [hp5tail] at hz5
            simp only [List.mem_singleton] at hz5
            subst z
            have h1 := hrange1 _ hz1
            have hnpos : 0 < (n : ℤ) := by exact_mod_cast hn
            omega)
    simpa only [hroute] using hrouteBuilt
  exact hroutePath

end PottsContinuity.FKC.FiniteFK
