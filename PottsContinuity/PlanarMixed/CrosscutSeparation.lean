module

public import PottsContinuity.PlanarMixed.CrosscutBottomOrder
public import PottsContinuity.PlanarTopology.RectangleIntersection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-! Walk separation by disjoint ordered bottom-to-top square crossings.
Only the paths, their actual supports, and bottom starting-point order occur
in the premises. All three ordered-cut separation facts follow geometrically.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PlanarTopology

section
variable (N : ℤ) (hN : 0 ≤ N) (a b : ℤ) {t u : LatticeVertex}
variable (p : squareLattice.Walk (a,0) t) (q : squareLattice.Walk (b,0) u)
variable (hab : a < b)
variable (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N)
variable (hq : ∀ z ∈ q.support, 0 ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N)
variable (ht : t.2 = N) (hu : u.2 = N)
variable (hdis : ∀ z ∈ p.support, z ∉ q.support)
include hN hab hp hq ht hu hdis

/-- Any walk from the square's left side to the right crossing meets the
left crossing. No monotonicity or simplicity of either crossing is assumed. -/
theorem crosscuts_left_to_second_hits_first {x z : LatticeVertex}
    (r : squareLattice.Walk x z) (hx : x.1 = 0) (hz : z ∈ q.support)
    (hr : ∀ w ∈ r.support, 0 ≤ w.1 ∧ w.1 ≤ N ∧ 0 ≤ w.2 ∧ w.2 ≤ N) :
    ∃ w, w ∈ r.support ∧ w ∈ p.support := by
  classical
  have hb := hq (b,0) q.start_mem_support
  have hbN : b ≤ N := hb.2.1
  obtain ⟨row, hrow⟩ := horizontal_walk_between b N 0
  have hrow' : ∀ w ∈ row.support, b ≤ w.1 ∧ w.1 ≤ N ∧ w.2 = 0 := by
    simpa only [min_eq_left hbN, max_eq_right hbN] using hrow
  let Q := (q.takeUntil z hz).reverse
  have hQs : ∀ w ∈ Q.support, w ∈ q.support := by
    intro w hw
    have hw' : w ∈ (q.takeUntil z hz).support := by
      simpa only [Q, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hw
    exact q.support_takeUntil_subset_support hz hw'
  let P := (r.append Q).append row
  have hP : ∀ w ∈ P.support, 0 ≤ w.1 ∧ w.1 ≤ N ∧ 0 ≤ w.2 ∧ w.2 ≤ N := by
    intro w hw
    change w ∈ ((r.append Q).append row).support at hw
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with (hw | hw) | hw
    · exact hr w hw
    · exact hq w (hQs w hw)
    · have h := hrow' w hw
      dsimp at hb
      omega
  obtain ⟨w, hwP, hwp⟩ := rectangle_walks_common_vertex P p hN hN hP hp hx rfl rfl ht
  change w ∈ ((r.append Q).append row).support at hwP
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hwP
  rcases hwP with (hwr | hwQ) | hwrow
  · exact ⟨w, hwr, hwp⟩
  · exact (hdis w hwp (hQs w hwQ)).elim
  · have h := hrow' w hwrow
    have hlt := (disjoint_crosscuts_bottom_order N hN a b p q hab hp hq ht hu hdis).1 w hwp h.2.2
    omega

/-- Any walk from the left crossing to the square's right side meets the
right crossing, with repeated boundary contacts still permitted. -/
theorem crosscuts_first_to_right_hits_second {z x : LatticeVertex}
    (r : squareLattice.Walk z x) (hz : z ∈ p.support) (hx : x.1 = N)
    (hr : ∀ w ∈ r.support, 0 ≤ w.1 ∧ w.1 ≤ N ∧ 0 ≤ w.2 ∧ w.2 ≤ N) :
    ∃ w, w ∈ r.support ∧ w ∈ q.support := by
  classical
  have ha := hp (a,0) p.start_mem_support
  have ha0 : 0 ≤ a := ha.1
  obtain ⟨row, hrow⟩ := horizontal_walk_between 0 a 0
  have hrow' : ∀ w ∈ row.support, 0 ≤ w.1 ∧ w.1 ≤ a ∧ w.2 = 0 := by
    simpa only [min_eq_left ha0, max_eq_right ha0] using hrow
  let Q := p.takeUntil z hz
  have hQs : ∀ w ∈ Q.support, w ∈ p.support := by
    intro w hw
    exact p.support_takeUntil_subset_support hz hw
  let P := (row.append Q).append r
  have hP : ∀ w ∈ P.support, 0 ≤ w.1 ∧ w.1 ≤ N ∧ 0 ≤ w.2 ∧ w.2 ≤ N := by
    intro w hw
    change w ∈ ((row.append Q).append r).support at hw
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with (hw | hw) | hw
    · have h := hrow' w hw
      dsimp at ha
      omega
    · exact hp w (hQs w hw)
    · exact hr w hw
  obtain ⟨w, hwP, hwq⟩ := rectangle_walks_common_vertex P q hN hN hP hq rfl hx rfl hu
  change w ∈ ((row.append Q).append r).support at hwP
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hwP
  rcases hwP with (hwrow | hwQ) | hwr
  · have h := hrow' w hwrow
    have hlt := (disjoint_crosscuts_bottom_order N hN a b p q hab hp hq ht hu hdis).2 w hwq h.2.2
    omega
  · exact (hdis w (hQs w hwQ) hwq).elim
  · exact ⟨w, hwr, hwq⟩

end
end PottsContinuity.PlanarMixed
