-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPrimalEdgeIntersections.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPrimalEdgeWalk
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedOwner
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCap
public import PottsContinuity.FKC.Medial.ParafermionicCoverPorts
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

private theorem walk_support_y_eq_of_compassDirections
    {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) (d : Fin 4)
    (hhor : d.val = 0 ∨ d.val = 2)
    (hdir : parafermionicCoverWalkCompassDirections p = List.replicate p.length d)
    (z : ParafermionicCoverVertex) (hz : z ∈ p.support) : z.1.2 = u.1.2 := by
  induction p with
  | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      rfl
  | @cons a b c hab tail ih =>
      simp only [parafermionicCoverWalkCompassDirections_cons, Walk.length_cons,
        List.replicate_succ] at hdir
      rcases List.cons.inj hdir with ⟨hhead, htail⟩
      simp only [Walk.support_cons, List.mem_cons] at hz
      have hstep : b.1.2 = a.1.2 := by
        have hn := parafermionicCoverCompassDirection_neighbor a b hab
        have hn' : parafermionicCoverCompassNeighbor a d = b := by
          rw [hhead] at hn
          exact hn
        rcases hhor with h0 | h2
        · have hd : d = 0 := Fin.ext h0
          rw [hd] at hn'
          have hy := congrArg (fun w : ParafermionicCoverVertex => w.1.2) hn'
          simpa [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
            parafermionicCoverNeighborLift, parafermionicCoverSheetShift] using hy.symm
        · have hd : d = 2 := Fin.ext h2
          rw [hd] at hn'
          have hy := congrArg (fun w : ParafermionicCoverVertex => w.1.2) hn'
          simpa [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
            parafermionicCoverNeighborLift, parafermionicCoverSheetShift] using hy.symm
      rcases hz with rfl | hz
      · rfl
      · exact (ih htail hz).trans hstep

private theorem walk_support_x_eq_of_compassDirections
    {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) (d : Fin 4)
    (hvert : d.val = 1 ∨ d.val = 3)
    (hdir : parafermionicCoverWalkCompassDirections p = List.replicate p.length d)
    (z : ParafermionicCoverVertex) (hz : z ∈ p.support) : z.1.1 = u.1.1 := by
  induction p with
  | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      rfl
  | @cons a b c hab tail ih =>
      simp only [parafermionicCoverWalkCompassDirections_cons, Walk.length_cons,
        List.replicate_succ] at hdir
      rcases List.cons.inj hdir with ⟨hhead, htail⟩
      simp only [Walk.support_cons, List.mem_cons] at hz
      have hstep : b.1.1 = a.1.1 := by
        have hn := parafermionicCoverCompassDirection_neighbor a b hab
        have hn' : parafermionicCoverCompassNeighbor a d = b := by
          rw [hhead] at hn
          exact hn
        rcases hvert with h1 | h3
        · have hd : d = 1 := Fin.ext h1
          rw [hd] at hn'
          have hx := congrArg (fun w : ParafermionicCoverVertex => w.1.1) hn'
          simpa [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
            parafermionicCoverNeighborLift, parafermionicCoverSheetShift] using hx.symm
        · have hd : d = 3 := Fin.ext h3
          rw [hd] at hn'
          have hx := congrArg (fun w : ParafermionicCoverVertex => w.1.1) hn'
          simpa [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
            parafermionicCoverNeighborLift, parafermionicCoverSheetShift] using hx.symm
      rcases hz with rfl | hz
      · rfl
      · exact (ih htail hz).trans hstep

theorem parafermionicCoverRefinedPrimalEdgeWalk_support_modulus
    (u : ParafermionicCoverVertex) (d : Fin 4) (z : ParafermionicCoverVertex)
    (hz : z ∈ (parafermionicCoverRefinedPrimalEdgeWalk u d).support) :
    z.1.1 % 9 = 5 ∨ z.1.2 % 9 = 4 := by
  have hlen := parafermionicCoverRefinedPrimalEdgeWalk_length u d
  have hdir := parafermionicCoverRefinedPrimalEdgeWalk_compassDirections u d
  have hdir' : parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedPrimalEdgeWalk u d) =
        List.replicate (parafermionicCoverRefinedPrimalEdgeWalk u d).length d := by
    rw [hlen]
    exact hdir
  fin_cases d
  · right
    have hy := walk_support_y_eq_of_compassDirections
      (parafermionicCoverRefinedPrimalEdgeWalk u 0) 0 (by norm_num)
      (by simpa using hdir') z hz
    rw [hy]
    simp [parafermionicCoverRefinedCoarseCenter]
  · left
    have hx := walk_support_x_eq_of_compassDirections
      (parafermionicCoverRefinedPrimalEdgeWalk u 1) 1 (by norm_num)
      (by simpa using hdir') z hz
    rw [hx]
    simp [parafermionicCoverRefinedCoarseCenter]
  · right
    have hy := walk_support_y_eq_of_compassDirections
      (parafermionicCoverRefinedPrimalEdgeWalk u 2) 2 (by norm_num)
      (by simpa using hdir') z hz
    rw [hy]
    simp [parafermionicCoverRefinedCoarseCenter]
  · left
    have hx := walk_support_x_eq_of_compassDirections
      (parafermionicCoverRefinedPrimalEdgeWalk u 3) 3 (by norm_num)
      (by simpa using hdir') z hz
    rw [hx]
    simp [parafermionicCoverRefinedCoarseCenter]

def refinedCompassRayVertex (d : Fin 4) (u : ParafermionicCoverVertex) : ℕ →
    ParafermionicCoverVertex
  | 0 => u
  | n + 1 => parafermionicCoverCompassNeighbor (refinedCompassRayVertex d u n) d

private theorem parafermionicCoverCompassNeighbor_east (z : ParafermionicCoverVertex) :
    parafermionicCoverCompassNeighbor z 0 =
      ((z.1.1 + 1, z.1.2), z.2 + if z.1.1 = 0 ∧ z.1.2 < 0 then 1 else 0) := by
  rcases z with ⟨⟨X, Y⟩, K⟩
  simp [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
    parafermionicCoverNeighborLift, parafermionicCoverSheetShift]; omega

private theorem refinedCompassRayVertex_east_formula
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    refinedCompassRayVertex 0 ((9 * x - 4, 9 * y + 4), k) j =
      ((9 * x - 4 + (j : ℤ), 9 * y + 4),
        k + if x = 0 ∧ y < 0 ∧ 5 ≤ j then 1 else 0) := by
  induction j with
  | zero => simp [refinedCompassRayVertex]
  | succ j ih =>
      rw [refinedCompassRayVertex, ih (by omega : j ≤ 9)]
      rw [parafermionicCoverCompassNeighbor_east]
      have hY : (9 * y + 4 < 0) ↔ y < 0 := by omega
      by_cases hx : x = 0
      · subst x
        by_cases hy : y < 0
        · by_cases hj4 : j = 4
          · have hcross : -4 + (j : ℤ) = 0 := by omega
            simp [hj4, hy, hY]
          · have hcross : -4 + (j : ℤ) ≠ 0 := by
              intro hc
              apply hj4
              omega
            simp [hy, hY, hcross]; omega
        · simp [hy, hY]
          omega
      · simp [hx]
        omega

private theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_east_map
    (u : ParafermionicCoverVertex) :
    parafermionicCoverRefinedPrimalEdgeWalkPoints u 0 =
      (List.range 10).map
        (refinedCompassRayVertex 0 (parafermionicCoverRefinedCoarseCenter u)) := by
  rcases u with ⟨⟨x,y⟩,k⟩
  rfl

theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_east_coordinate
    (x y k : ℤ) (z : ParafermionicCoverVertex)
    (hz : z ∈ parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 0) :
    ∃ j : ℕ, j ≤ 9 ∧
      z = ((9 * x - 4 + (j : ℤ), 9 * y + 4),
        k + if x = 0 ∧ y < 0 ∧ 5 ≤ j then 1 else 0) := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_east_map] at hz
  simp only [List.mem_map, List.mem_range] at hz
  rcases hz with ⟨j, hj, hzj⟩
  refine ⟨j, by omega, ?_⟩
  rw [← hzj]
  exact refinedCompassRayVertex_east_formula x y k j (by omega)

theorem parafermionicCoverRefinedClosedCapMiddle_east_portEdge_val
    (u : ParafermionicCoverVertex) (c : ParafermionicCoverPort)
    (hc : parafermionicCoverRefinedClosedCapMiddle c ∈
      (parafermionicCoverRefinedPrimalEdgeWalk u 0).support) :
    (parafermionicCoverPortEdge c).val =
      s(u, parafermionicCoverCompassNeighbor u 0) := by
  rcases u with ⟨⟨ux, uy⟩, uk⟩
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rw [parafermionicCoverRefinedPrimalEdgeWalk_support] at hc
  cases ax
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_east_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.horizontal⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_horizontal] at hz
    simp only [Prod.mk.injEq] at hz
    rcases hz with ⟨⟨hx, hy⟩, hk⟩
    have hx' : x = ux := by omega
    have hy' : y = uy := by omega
    have hj' : j = (if tip then 5 else 4) := by
      cases tip <;> simp_all <;> omega
    subst x
    subst y
    subst j
    cases tip <;> cases side <;>
      simp_all [parafermionicCoverPortEdge_val, parafermionicCoverPortSourceSheet,
        parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverNeighborLift, parafermionicCoverSheetShift,
        LatticeBond.source, LatticeBond.target] <;> omega
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_east_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.vertical⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_vertical] at hz
    simp only [Prod.mk.injEq] at hz
    omega

private theorem parafermionicCoverCompassNeighbor_north (z : ParafermionicCoverVertex) :
    parafermionicCoverCompassNeighbor z 1 = ((z.1.1, z.1.2 + 1), z.2) := by
  rcases z with ⟨⟨X, Y⟩, K⟩
  simp [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
    parafermionicCoverNeighborLift, parafermionicCoverSheetShift]

private theorem parafermionicCoverCompassNeighbor_south (z : ParafermionicCoverVertex) :
    parafermionicCoverCompassNeighbor z 3 = ((z.1.1, z.1.2 - 1), z.2) := by
  rcases z with ⟨⟨X, Y⟩, K⟩
  simp [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
    parafermionicCoverNeighborLift, parafermionicCoverSheetShift]; omega

private theorem refinedCompassRayVertex_north_formula
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    refinedCompassRayVertex 1 ((9 * x - 4, 9 * y + 4), k) j =
      ((9 * x - 4, 9 * y + 4 + (j : ℤ)), k) := by
  induction j with
  | zero => simp [refinedCompassRayVertex]
  | succ j ih =>
      rw [refinedCompassRayVertex, ih (by omega : j ≤ 9),
        parafermionicCoverCompassNeighbor_north]
      congr 1; push_cast; ring_nf

private theorem refinedCompassRayVertex_south_formula
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    refinedCompassRayVertex 3 ((9 * x - 4, 9 * y + 4), k) j =
      ((9 * x - 4, 9 * y + 4 - (j : ℤ)), k) := by
  induction j with
  | zero => simp [refinedCompassRayVertex]
  | succ j ih =>
      rw [refinedCompassRayVertex, ih (by omega : j ≤ 9),
        parafermionicCoverCompassNeighbor_south]
      congr 1; push_cast; ring_nf

private theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_north_map
    (u : ParafermionicCoverVertex) :
    parafermionicCoverRefinedPrimalEdgeWalkPoints u 1 =
      (List.range 10).map
        (refinedCompassRayVertex 1 (parafermionicCoverRefinedCoarseCenter u)) := by
  rcases u with ⟨⟨x,y⟩,k⟩
  rfl

private theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_south_map
    (u : ParafermionicCoverVertex) :
    parafermionicCoverRefinedPrimalEdgeWalkPoints u 3 =
      (List.range 10).map
        (refinedCompassRayVertex 3 (parafermionicCoverRefinedCoarseCenter u)) := by
  rcases u with ⟨⟨x,y⟩,k⟩
  rfl

theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_north_coordinate
    (x y k : ℤ) (z : ParafermionicCoverVertex)
    (hz : z ∈ parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 1) :
    ∃ j : ℕ, j ≤ 9 ∧ z = ((9 * x - 4, 9 * y + 4 + (j : ℤ)), k) := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_north_map] at hz
  simp only [List.mem_map, List.mem_range] at hz
  rcases hz with ⟨j, hj, hzj⟩
  refine ⟨j, by omega, ?_⟩
  rw [← hzj]
  exact refinedCompassRayVertex_north_formula x y k j (by omega)

theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_south_coordinate
    (x y k : ℤ) (z : ParafermionicCoverVertex)
    (hz : z ∈ parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 3) :
    ∃ j : ℕ, j ≤ 9 ∧ z = ((9 * x - 4, 9 * y + 4 - (j : ℤ)), k) := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_south_map] at hz
  simp only [List.mem_map, List.mem_range] at hz
  rcases hz with ⟨j, hj, hzj⟩
  refine ⟨j, by omega, ?_⟩
  rw [← hzj]
  exact refinedCompassRayVertex_south_formula x y k j (by omega)

theorem parafermionicCoverRefinedClosedCapMiddle_north_portEdge_val
    (u : ParafermionicCoverVertex) (c : ParafermionicCoverPort)
    (hc : parafermionicCoverRefinedClosedCapMiddle c ∈
      (parafermionicCoverRefinedPrimalEdgeWalk u 1).support) :
    (parafermionicCoverPortEdge c).val =
      s(u, parafermionicCoverCompassNeighbor u 1) := by
  rcases u with ⟨⟨ux, uy⟩, uk⟩
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rw [parafermionicCoverRefinedPrimalEdgeWalk_support] at hc
  cases ax
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_north_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.horizontal⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_horizontal] at hz
    simp only [Prod.mk.injEq] at hz
    omega
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_north_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.vertical⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_vertical] at hz
    simp only [Prod.mk.injEq] at hz
    rcases hz with ⟨⟨hx, hy⟩, hk⟩
    have hx' : x = ux := by omega
    have hy' : y = uy := by omega
    have hj' : j = (if tip then 5 else 4) := by
      cases tip <;> simp_all <;> omega
    subst x
    subst y
    subst j
    have hk' : k = uk := hk
    subst k
    cases tip <;> cases side <;>
      simp_all [parafermionicCoverPortEdge_val, parafermionicCoverPortSourceSheet,
        parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverNeighborLift, parafermionicCoverSheetShift,
        LatticeBond.source, LatticeBond.target]

theorem parafermionicCoverRefinedClosedCapMiddle_south_portEdge_val
    (u : ParafermionicCoverVertex) (c : ParafermionicCoverPort)
    (hc : parafermionicCoverRefinedClosedCapMiddle c ∈
      (parafermionicCoverRefinedPrimalEdgeWalk u 3).support) :
    (parafermionicCoverPortEdge c).val =
      s(u, parafermionicCoverCompassNeighbor u 3) := by
  rcases u with ⟨⟨ux, uy⟩, uk⟩
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rw [parafermionicCoverRefinedPrimalEdgeWalk_support] at hc
  cases ax
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_south_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.horizontal⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_horizontal] at hz
    simp only [Prod.mk.injEq] at hz
    omega
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_south_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.vertical⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_vertical] at hz
    simp only [Prod.mk.injEq] at hz
    rcases hz with ⟨⟨hx, hy⟩, hk⟩
    have hx' : x = ux := by omega
    have hy' : y = uy - 1 := by omega
    have hj' : j = (if tip then 4 else 5) := by
      cases tip <;> simp_all <;> omega
    subst x
    subst y
    subst j
    have hk' : k = uk := hk
    subst k
    cases tip <;> cases side <;>
      simp_all [parafermionicCoverPortEdge_val, parafermionicCoverPortSourceSheet,
        parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverNeighborLift, parafermionicCoverSheetShift,
        LatticeBond.source, LatticeBond.target] <;> omega

private theorem parafermionicCoverCompassNeighbor_west (z : ParafermionicCoverVertex) :
    parafermionicCoverCompassNeighbor z 2 =
      ((z.1.1 - 1, z.1.2), z.2 - if z.1.1 = 1 ∧ z.1.2 < 0 then 1 else 0) := by
  rcases z with ⟨⟨X, Y⟩, K⟩
  simp [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
    parafermionicCoverNeighborLift, parafermionicCoverSheetShift]; omega

private theorem refinedCompassRayVertex_west_formula
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    refinedCompassRayVertex 2 ((9 * x - 4, 9 * y + 4), k) j =
      ((9 * x - 4 - (j : ℤ), 9 * y + 4),
        k - if x = 1 ∧ y < 0 ∧ 5 ≤ j then 1 else 0) := by
  induction j with
  | zero => simp [refinedCompassRayVertex]
  | succ j ih =>
      rw [refinedCompassRayVertex, ih (by omega : j ≤ 9)]
      rw [parafermionicCoverCompassNeighbor_west]
      have hY : (9 * y + 4 < 0) ↔ y < 0 := by omega
      by_cases hx : x = 1
      · subst x
        by_cases hy : y < 0
        · by_cases hj4 : j = 4
          · have hcross : 5 - (j : ℤ) = 1 := by omega
            simp [hj4, hy, hY]
          · have hcross : 5 - (j : ℤ) ≠ 1 := by
              intro hc
              apply hj4
              omega
            simp [hy, hY, hcross]; omega
        · simp [hy, hY]; omega
      · simp [hx]; omega

private theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_west_map
    (u : ParafermionicCoverVertex) :
    parafermionicCoverRefinedPrimalEdgeWalkPoints u 2 =
      (List.range 10).map
        (refinedCompassRayVertex 2 (parafermionicCoverRefinedCoarseCenter u)) := by
  rcases u with ⟨⟨x,y⟩,k⟩
  rfl

theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_west_coordinate
    (x y k : ℤ) (z : ParafermionicCoverVertex)
    (hz : z ∈ parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 2) :
    ∃ j : ℕ, j ≤ 9 ∧
      z = ((9 * x - 4 - (j : ℤ), 9 * y + 4),
        k - if x = 1 ∧ y < 0 ∧ 5 ≤ j then 1 else 0) := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_west_map] at hz
  simp only [List.mem_map, List.mem_range] at hz
  rcases hz with ⟨j, hj, hzj⟩
  refine ⟨j, by omega, ?_⟩
  rw [← hzj]
  exact refinedCompassRayVertex_west_formula x y k j (by omega)

theorem parafermionicCoverRefinedClosedCapMiddle_west_portEdge_val
    (u : ParafermionicCoverVertex) (c : ParafermionicCoverPort)
    (hc : parafermionicCoverRefinedClosedCapMiddle c ∈
      (parafermionicCoverRefinedPrimalEdgeWalk u 2).support) :
    (parafermionicCoverPortEdge c).val =
      s(u, parafermionicCoverCompassNeighbor u 2) := by
  rcases u with ⟨⟨ux, uy⟩, uk⟩
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rw [parafermionicCoverRefinedPrimalEdgeWalk_support] at hc
  cases ax
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_west_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.horizontal⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_horizontal] at hz
    simp only [Prod.mk.injEq] at hz
    rcases hz with ⟨⟨hx, hy⟩, hk⟩
    have hy' : y = uy := by omega
    have hx' : x = ux - 1 := by omega
    have hj' : j = (if tip then 4 else 5) := by
      cases tip <;> simp_all <;> omega
    subst x
    subst y
    subst j
    cases tip <;> cases side <;>
      simp_all [parafermionicCoverPortEdge_val, parafermionicCoverPortSourceSheet,
        parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverNeighborLift, parafermionicCoverSheetShift,
        LatticeBond.source, LatticeBond.target] <;> omega
  · obtain ⟨j, hj, hz⟩ :=
      parafermionicCoverRefinedPrimalEdgeWalkPoints_west_coordinate ux uy uk
        (parafermionicCoverRefinedClosedCapMiddle
          ((⟨⟨(x,y), LatticeAxis.vertical⟩, tip, side⟩ : LatticePort), k)) hc
    rw [parafermionicCoverRefinedClosedCapMiddle_vertical] at hz
    simp only [Prod.mk.injEq] at hz
    omega

theorem parafermionicCoverRefinedClosedCapMiddle_walk_portEdge
    (u : ParafermionicCoverVertex) (d : Fin 4) (c : ParafermionicCoverPort)
    (hc : parafermionicCoverRefinedClosedCapMiddle c ∈
      (parafermionicCoverRefinedPrimalEdgeWalk u d).support) :
    parafermionicCoverPortEdge c =
      (⟨s(u, parafermionicCoverCompassNeighbor u d), by
        apply parafermionicCoverGraph.mem_edgeSet.mpr
        exact ⟨(parafermionicCoverCompassNeighbor_adj u d).1, rfl⟩⟩ :
        parafermionicCoverGraph.edgeSet) := by
  apply Subtype.ext
  fin_cases d
  · exact parafermionicCoverRefinedClosedCapMiddle_east_portEdge_val u c hc
  · exact parafermionicCoverRefinedClosedCapMiddle_north_portEdge_val u c hc
  · exact parafermionicCoverRefinedClosedCapMiddle_west_portEdge_val u c hc
  · exact parafermionicCoverRefinedClosedCapMiddle_south_portEdge_val u c hc

/-- Every indexed east ray point occurs in the actual public point list. -/
theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_east_mem_of_index
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    ((9 * x - 4 + (j : ℤ), 9 * y + 4),
      k + if x = 0 ∧ y < 0 ∧ 5 ≤ j then 1 else 0) ∈
      parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 0 := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_east_map]
  apply List.mem_map.mpr
  exact ⟨j, by simp [List.mem_range]; omega,
    refinedCompassRayVertex_east_formula x y k j hj⟩

/-- Every indexed north ray point occurs in the actual public point list. -/
theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_north_mem_of_index
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    ((9 * x - 4, 9 * y + 4 + (j : ℤ)), k) ∈
      parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 1 := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_north_map]
  apply List.mem_map.mpr
  exact ⟨j, by simp [List.mem_range]; omega,
    refinedCompassRayVertex_north_formula x y k j hj⟩

/-- Every indexed west ray point occurs in the actual public point list. -/
theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_west_mem_of_index
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    ((9 * x - 4 - (j : ℤ), 9 * y + 4),
      k - if x = 1 ∧ y < 0 ∧ 5 ≤ j then 1 else 0) ∈
      parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 2 := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_west_map]
  apply List.mem_map.mpr
  exact ⟨j, by simp [List.mem_range]; omega,
    refinedCompassRayVertex_west_formula x y k j hj⟩

/-- Every indexed south ray point occurs in the actual public point list. -/
theorem parafermionicCoverRefinedPrimalEdgeWalkPoints_south_mem_of_index
    (x y k : ℤ) (j : ℕ) (hj : j ≤ 9) :
    ((9 * x - 4, 9 * y + 4 - (j : ℤ)), k) ∈
      parafermionicCoverRefinedPrimalEdgeWalkPoints ((x,y),k) 3 := by
  rw [parafermionicCoverRefinedPrimalEdgeWalkPoints_south_map]
  apply List.mem_map.mpr
  exact ⟨j, by simp [List.mem_range]; omega,
    refinedCompassRayVertex_south_formula x y k j hj⟩

end PottsContinuity.FKC.Medial

