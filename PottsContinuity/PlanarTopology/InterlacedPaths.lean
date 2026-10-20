module

public import PottsContinuity.PlanarTopology.DisjointRayIndex
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Data.Int.Star

/-! Interlaced paths on a half-plane boundary must share an original vertex.
The proof closes one path below the boundary and computes a discrete ray index.
No Jordan parametrization or simplicity premise is required.
-/

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality

/-- Ray index is additive under chronological concatenation of walks. -/
theorem rayIndex_append (x : LatticeVertex) {u v w : LatticeVertex}
    (p : squareLattice.Walk u v) (q : squareLattice.Walk v w) :
    rayIndex x (p.append q) = rayIndex x p + rayIndex x q := by
  induction p with
  | nil => simp [rayIndex]
  | cons h p ih => simp only [SimpleGraph.Walk.cons_append, rayIndex, ih, add_assoc]

private theorem exists_row_walk (a y : ℤ) (n : ℕ) :
    ∃ p : squareLattice.Walk (a,y) (a + (n : ℤ),y),
      ∀ z ∈ p.support, z.2 = y := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    exact ⟨.nil, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    have hstep : squareLattice.Adj (a + (n : ℤ), y) (a + ((n+1 : ℕ) : ℤ), y) := by
      simp [squareLattice_adj_iff, Nat.cast_add, add_assoc]
    refine ⟨p.concat hstep, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_concat] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hp z hz
    · have hz := List.mem_singleton.mp hz
      subst z
      rfl

/-- Two upper-half-plane walks with alternating endpoints on the bottom line intersect.
Endpoint equalities are allowed. The witness lies on both original walk supports. -/
theorem upperHalfPlane_interlaced_walks_intersect
    (a b c d : ℤ)
    (p : squareLattice.Walk (a,0) (c,0))
    (q : squareLattice.Walk (b,0) (d,0))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hp : ∀ z ∈ p.support, 0 ≤ z.2)
    (hq : ∀ z ∈ q.support, 0 ≤ z.2) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  by_cases hab' : a = b
  · subst b
    exact ⟨(a,0), p.start_mem_support, q.start_mem_support⟩
  by_cases hbc' : b = c
  · subst c
    exact ⟨(b,0), p.end_mem_support, q.start_mem_support⟩
  by_cases hcd' : c = d
  · subst d
    exact ⟨(c,0), p.end_mem_support, q.end_mem_support⟩
  by_contra hno
  have hdis : ∀ z ∈ q.support, z ∉ p.support := by
    intro z hz hzp
    exact hno ⟨z, hzp, hz⟩
  have hac : a ≤ c := hab.trans hbc
  have hnat : a + (((c-a).toNat : ℕ) : ℤ) = c := by omega
  have hrow := exists_row_walk a (-1) (c-a).toNat
  rw [hnat] at hrow
  obtain ⟨r₀, hr₀⟩ := hrow
  let r := r₀.reverse
  have hr : ∀ z ∈ r.support, z.2 = -1 := by
    intro z hz
    apply hr₀ z
    simpa only [r, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  have hd : squareLattice.Adj (c,0) (c,-1) := by
    rw [squareLattice_adj_iff]
    norm_num
  have hu : squareLattice.Adj (a,-1) (a,0) := by
    rw [squareLattice_adj_iff]
    norm_num
  let down := hd.toWalk
  let up := hu.toWalk
  let C := (p.append down).append (r.append up)
  have hCdis : ∀ z ∈ q.support, z ∉ C.support := by
    intro z hz hC
    change z ∈ ((p.append down).append (r.append up)).support at hC
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hC
    rcases hC with (hzp | hzd) | (hzr | hzu)
    · exact hdis z hz hzp
    · have hzd' : z = (c,0) ∨ z = (c,-1) := by simpa [down] using hzd
      rcases hzd' with rfl | rfl
      · exact hdis _ hz p.end_mem_support
      · have := hq _ hz; norm_num at this
    · have hzlow := hr z hzr
      have hzhigh := hq z hz
      omega
    · have hzu' : z = (a,-1) ∨ z = (a,0) := by simpa [up] using hzu
      rcases hzu' with rfl | rfl
      · have := hq _ hz; norm_num at this
      · exact hdis _ hz p.start_mem_support
  have hidx := rayIndex_eq_of_disjoint_support C q hCdis
  have hpzero (x : ℤ) : rayIndex (x,0) p = 0 := by
    apply rayIndex_zero_of_level (x,0) p 0
    intro z hz
    simp only [ite_eq_right (not_lt.mpr (hp z hz))]
  have hrzero (x : ℤ) : rayIndex (x,0) r = 0 := by
    apply rayIndex_zero_of_level (x,0) r 1
    intro z hz
    rw [hr z hz]
    norm_num
  have hformula (x : ℤ) : rayIndex (x,0) C =
      (if x ≤ a then 1 else 0) - (if x ≤ c then 1 else 0) := by
    simp [C, rayIndex_append, hpzero, hrzero, down, up, rayIndex, rayStep]
    split_ifs <;> omega
  rw [hformula, hformula] at hidx
  simp only [ite_eq_left hbc, ite_eq_right (by omega : ¬ b ≤ a),
    ite_eq_right (by omega : ¬ d ≤ c), ite_eq_right (by omega : ¬ d ≤ a)] at hidx
  omega

end PottsContinuity.PlanarTopology
