-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/OutsidePathLocalization.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Tactic

@[expose] public section

open SimpleGraph

namespace PottsContinuity.FKC.Medial

private theorem exists_index_of_mem_take_support
    {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (i : ℕ) {z : V} (hz : z ∈ (p.take i).support) :
    ∃ j ≤ i, p.getVert j = z := by
  rw [SimpleGraph.Walk.support_take] at hz
  obtain ⟨j, hj, hzTake⟩ := List.mem_iff_getElem.mp hz
  rw [List.length_take] at hj
  have hjltI : j < i + 1 := lt_of_lt_of_le hj (Nat.min_le_left _ _)
  have hjltSupport : j < p.support.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
  have hji : j ≤ i := by omega
  have hjleLength : j ≤ p.length := by
    rw [p.length_support] at hjltSupport
    omega
  have hzElem : p.support[j]'(by rw [p.length_support]; omega) = z := by
    simpa using hzTake
  refine ⟨j, hji, ?_⟩
  rw [p.getVert_eq_support_getElem hjleLength]
  exact hzElem

/-- A walk from outside H to x can be trimmed at its last outside vertex.
The resulting walk starts at an outside neighbor of H and thereafter stays in
H; avoidance of W is preserved. -/
theorem exists_avoiding_walk_from_outside_neighbor_iff
    {V : Type*} (G : SimpleGraph V) (H W : Set V) {x : V} (hx : x ∈ H) :
    (∃ y : V, y ∉ H ∧ ∃ p : G.Walk y x,
      ∀ z ∈ p.support, z ∉ W) ↔
    (∃ z : V, z ∉ H ∧ (∃ w ∈ H, G.Adj z w) ∧
      ∃ p : G.Walk z x, (∀ v ∈ p.support, v ∉ W) ∧
        ∀ v ∈ p.support, v ∈ H ∨ v = z) := by
  classical
  constructor
  · rintro ⟨y, hy, p, hpW⟩
    let q := p.reverse
    have hend : ¬ q.getVert q.length ∈ H := by
      rw [q.getVert_length]
      exact hy
    have hexit : ∃ i : ℕ, ¬ q.getVert i ∈ H := ⟨q.length, hend⟩
    let i := Nat.find hexit
    have hiOutside : ¬ q.getVert i ∈ H := Nat.find_spec hexit
    have hiLe : i ≤ q.length := Nat.find_min' hexit hend
    have hiPos : 0 < i := by
      by_contra hnot
      have hi0 : i = 0 := by omega
      have hzero : ¬ q.getVert 0 ∈ H := by simpa [i, hi0] using hiOutside
      have hstart : q.getVert 0 ∈ H := by simpa [q] using hx
      exact hzero hstart
    have hprev : q.getVert (i - 1) ∈ H := by
      by_contra hnot
      have hfirst := Nat.find_min hexit (m := i - 1) (by omega)
      exact hfirst hnot
    have hstep : G.Adj (q.getVert (i - 1)) (q.getVert i) := by
      have hidx : i - 1 < q.length := by omega
      have hadj := q.adj_getVert_succ hidx
      convert hadj using 1; congr 1; omega
    let z := q.getVert i
    let r : G.Walk z x := (q.take i).reverse
    have hsupport : ∀ v ∈ r.support, v ∈ H ∨ v = z := by
      intro v hv
      have hv' : v ∈ (q.take i).support := by
        simpa [r, SimpleGraph.Walk.support_reverse] using hv
      obtain ⟨j, hji, hjv⟩ := exists_index_of_mem_take_support q i hv'
      by_cases hji' : j = i
      · right
        simpa [z, hji'] using hjv.symm
      · left
        have hjlt : j < i := by omega
        have hjH : q.getVert j ∈ H := not_not.mp (Nat.find_min hexit hjlt)
        simpa [hjv] using hjH
    have havoid : ∀ v ∈ r.support, v ∉ W := by
      intro v hv
      have hv' : v ∈ p.support := by
        have hvq : v ∈ q.support := by
          have hvTake : v ∈ (q.take i).support := by
            simpa [r, SimpleGraph.Walk.support_reverse] using hv
          rw [SimpleGraph.Walk.support_take] at hvTake
          exact List.mem_of_mem_take hvTake
        simpa [q, SimpleGraph.Walk.support_reverse] using hvq
      exact hpW v hv'
    refine ⟨z, hiOutside, ?_, r, havoid, hsupport⟩
    refine ⟨q.getVert (i - 1), hprev, ?_⟩
    exact hstep.symm
  · rintro ⟨z, hz, ⟨w, hwH, hzw⟩, p, hpW, _⟩
    exact ⟨z, hz, p, hpW⟩

end PottsContinuity.FKC.Medial
