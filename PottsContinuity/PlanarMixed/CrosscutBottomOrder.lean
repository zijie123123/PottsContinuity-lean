module

public import PottsContinuity.PlanarTopology.InterlacedPaths
public import PottsContinuity.PlanarTopology.HorizontalWalks
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Bottom-boundary order of disjoint top crossings

Uses the interlaced-walk theorem `PlanarTopology.upperHalfPlane_interlaced_walks_intersect`.
Paths need not be simple and may return to the bottom boundary. This is deterministic
geometry of the actual source square, with no boundary partition or probability premise.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PlanarTopology

def swapLattice : squareLattice →g squareLattice where
  toFun z := (z.2,z.1)
  map_rel' := by
    intro u v h
    simp only [squareLattice_adj_iff] at h ⊢
    omega

/-- Extend a top vertex to the bottom just outside the right edge. Every
added vertex except the original endpoint is outside the closed square. -/
theorem crosscut_top_right_extension (N : ℤ) (hN : 0 ≤ N)
    (t : LatticeVertex) (ht : t.2 = N) (htx : 0 ≤ t.1 ∧ t.1 ≤ N) :
    ∃ e : squareLattice.Walk t (N+1,0),
      (∀ z ∈ e.support, 0 ≤ z.2) ∧
      ∀ z ∈ e.support, z = t ∨ N < z.1 ∨ N < z.2 := by
  obtain ⟨r, hr⟩ := horizontal_walk_between t.1 (N+1) (N+1)
  obtain ⟨v, hv⟩ := horizontal_walk_between 0 (N+1) (N+1)
  have hadj : squareLattice.Adj t (t.1,N+1) := by
    rw [squareLattice_adj_iff]
    dsimp
    omega
  let V : squareLattice.Walk (N+1,0) (N+1,N+1) :=
    (v.map swapLattice).copy rfl rfl
  have hsV : V.support = v.support.map swapLattice := by
    calc
      V.support = (v.map swapLattice).support := SimpleGraph.Walk.support_copy _ _ _
      _ = v.support.map swapLattice := SimpleGraph.Walk.support_map _ _
  let e := (hadj.toWalk.append r).append V.reverse
  have hs (z : LatticeVertex) (hz : z ∈ e.support) :
      z = t ∨ N < z.1 ∨ N < z.2 := by
    change z ∈ ((hadj.toWalk.append r).append V.reverse).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · have hz' : z = t ∨ z = (t.1,N+1) := by simpa using hz
      rcases hz' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (by dsimp; omega))
    · exact Or.inr (Or.inr (by have h := hr z hz; omega))
    · have hz' : z ∈ V.support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
      rw [hsV] at hz'
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz'
      have h := hv w hw
      exact Or.inr (Or.inl (by change N < w.2; omega))
  refine ⟨e, ?_, hs⟩
  intro z hz
  change z ∈ ((hadj.toWalk.append r).append V.reverse).support at hz
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with (hz | hz) | hz
  · have hz' : z = t ∨ z = (t.1,N+1) := by simpa using hz
    rcases hz' with rfl | rfl
    · omega
    · change 0 ≤ N+1
      omega
  · have h := hr z hz
    omega
  · have hz' : z ∈ V.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
    rw [hsV] at hz'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz'
    have h := hv w hw
    change 0 ≤ w.1
    simpa only [min_eq_left (by omega : (0 : ℤ) ≤ N+1)] using h.1

/-- A bottom excursion spanning the start of a bottom-to-top crossing meets
that crossing, including paths that revisit the boundary. -/
theorem bottom_excursion_meets_crosscut (N : ℤ) (hN : 0 ≤ N)
    (a b c : ℤ) {t : LatticeVertex}
    (p : squareLattice.Walk (a,0) (c,0))
    (q : squareLattice.Walk (b,0) t)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N)
    (hq : ∀ z ∈ q.support, 0 ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N)
    (ht : t.2 = N) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  have htb := hq t q.end_mem_support
  obtain ⟨e, he, hout⟩ := crosscut_top_right_extension N hN t ht ⟨htb.1, htb.2.1⟩
  obtain ⟨z, hzp, hzq⟩ := upperHalfPlane_interlaced_walks_intersect a b c (N+1)
    p (q.append e) hab hbc (by have h := hp (c,0) p.end_mem_support; dsimp at h; omega)
    (fun z hz => (hp z hz).2.2.1) (by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact (hq z hz).2.2.1
      · exact he z hz)
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzq
  rcases hzq with hzq | hze
  · exact ⟨z, hzp, hzq⟩
  · rcases hout z hze with rfl | hz | hz
    · exact ⟨_, hzp, q.end_mem_support⟩
    · have h := hp z hzp
      omega
    · have h := hp z hzp
      omega

/-- Every bottom contact of the left crossing precedes the right start,
and every bottom contact of the right crossing follows the left start. -/
theorem disjoint_crosscuts_bottom_order (N : ℤ) (hN : 0 ≤ N)
    (a b : ℤ) {t u : LatticeVertex}
    (p : squareLattice.Walk (a,0) t) (q : squareLattice.Walk (b,0) u)
    (hab : a < b)
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N)
    (hq : ∀ z ∈ q.support, 0 ≤ z.1 ∧ z.1 ≤ N ∧ 0 ≤ z.2 ∧ z.2 ≤ N)
    (ht : t.2 = N) (hu : u.2 = N)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    (∀ z ∈ p.support, z.2 = 0 → z.1 < b) ∧
      (∀ z ∈ q.support, z.2 = 0 → a < z.1) := by
  classical
  constructor
  · intro z hz hz0
    by_contra hn
    have he : z = (z.1,0) := Prod.ext rfl hz0
    let P := (p.takeUntil z hz).copy rfl he
    have hs : ∀ w ∈ P.support, w ∈ p.support := by
      intro w hw
      rw [SimpleGraph.Walk.support_copy] at hw
      exact p.support_takeUntil_subset_support hz hw
    obtain ⟨w, hwP, hwQ⟩ := bottom_excursion_meets_crosscut N hN a b z.1 P q
      (by omega) (by omega) (fun w hw => hp w (hs w hw)) hq hu
    exact hdis w (hs w hwP) hwQ
  · intro z hz hz0
    by_contra hn
    have he : z = (z.1,0) := Prod.ext rfl hz0
    let Q := ((q.takeUntil z hz).reverse).copy he rfl
    have hs : ∀ w ∈ Q.support, w ∈ q.support := by
      intro w hw
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] at hw
      exact q.support_takeUntil_subset_support hz hw
    obtain ⟨w, hwQ, hwP⟩ := bottom_excursion_meets_crosscut N hN z.1 a b Q p
      (by omega) (by omega) (fun w hw => hq w (hs w hw)) hp ht
    exact hdis w hwP (hs w hwQ)

end PottsContinuity.PlanarMixed
