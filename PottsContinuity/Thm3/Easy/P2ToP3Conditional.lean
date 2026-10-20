module

public import PottsContinuity.PD.Duality.Rectangle
public import PottsContinuity.PD.CorrLength.ConnectionEvents
public import PottsContinuity.PD.Defs.RCInfiniteOpenGraph
public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting
public import PottsContinuity.BD12.DualStripOpen
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.BD12

/-- Whole-plane connection from `x` to the vertex boundary of the radius-`n`
box centered at `x`. -/
def oneArmBoundaryEvent (x : LatticeVertex) (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ y ∈ PottsContinuity.PD.vertexBoundary (latticeBox x n),
    ω ∈ PottsContinuity.PD.CorrLength.connectionEvent x y}

private theorem reachable_rectangle_to_whole_plane
    (ω : LatticeConfiguration) (a : LatticeVertex) (w h : ℕ)
    {u v : RectangleVertex a w h}
    (huv : ((rcInfiniteOpenGraph ω).induce
      (latticeRectangle a w h : Set LatticeVertex)).Reachable u v) :
    (rcInfiniteOpenGraph ω).Reachable u.val v.val := by
  rcases huv with ⟨p⟩
  let f : (rcInfiniteOpenGraph ω).induce
      (latticeRectangle a w h : Set LatticeVertex) →g rcInfiniteOpenGraph ω :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hadj
        exact hadj }
  exact ⟨(p.map f).copy (by rfl) (by rfl)⟩

private theorem vertical_crossing_has_bottom_one_arm (n : ℕ)
    (ω : LatticeConfiguration)
    (hω : ω ∈ verticalRectangle (-(n : ℤ), 0) (2 * n) n) :
    ∃ x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) n},
      ω ∈ oneArmBoundaryEvent (x.val, 0) n := by
  rcases hω with ⟨u, v, hu, hv, huv⟩
  have hrectU : u.val ∈ latticeRectangle (-(n : ℤ), 0) (2 * n) n := u.property
  rw [mem_latticeRectangle] at hrectU
  have hxrange : -(n : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (n : ℤ) := by
    constructor <;> omega
  have hxy : u.val.2 = 0 := hu
  let x : LatticeVertex := (u.val.1, 0)
  have hxid : x = u.val := by
    exact Prod.ext rfl hxy.symm
  have hxmem : x.1 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) :=
    Finset.mem_Icc.mpr hxrange
  let S : Set LatticeVertex := latticeBox x n
  let g := rcInfiniteOpenGraph ω
  have hreachU : g.Reachable u.val v.val :=
    reachable_rectangle_to_whole_plane ω (-(n : ℤ), 0) (2 * n) n huv
  have hreach : g.Reachable x v.val := by
    rw [hxid]
    exact hreachU
  rcases hreach with ⟨p⟩
  have hxS : x ∈ S := by
    exact center_mem_latticeBox x n
  have hvcoord : v.val.2 = (n : ℤ) := by
    change v.val.2 = 0 + (n : ℤ) at hv
    omega
  by_cases hV : v.val ∈ S
  · have hboundary : v.val ∈ PottsContinuity.PD.vertexBoundary (latticeBox x n) := by
      refine ⟨hV, (v.val.1, v.val.2 + 1), ?_, ?_⟩
      · rw [squareLattice_adj_iff]
        exact Or.inr ⟨rfl, Or.inl rfl⟩
      · intro hy
        change v.val ∈ latticeBox x n at hV
        rw [mem_latticeBox] at hV
        rw [mem_latticeBox] at hy
        simp only [x] at hV hy
        omega
    have hconn : ω ∈ PottsContinuity.PD.CorrLength.connectionEvent x v.val := by
      rw [PottsContinuity.PD.CorrLength.connectionEvent_iff_rcInfiniteReachable]
      exact p.reachable
    exact ⟨⟨x.1, hxmem⟩, v.val, hboundary, hconn⟩
  · obtain ⟨z, hzS, p₀, hp₀S, y, hzy, hyS⟩ :=
      PottsContinuity.PD.RCInfinite.walk_prefix_to_boundary p hxS hV
    have hboundary : z ∈ PottsContinuity.PD.vertexBoundary (latticeBox x n) :=
      ⟨hzS, y, (PottsContinuity.PD.squareLattice.mem_edgeSet.mp
        ((rcInfiniteOpenGraph_adj ω z y).mp hzy).1), hyS⟩
    have hconn : ω ∈ PottsContinuity.PD.CorrLength.connectionEvent x z := by
      rw [PottsContinuity.PD.CorrLength.connectionEvent_iff_rcInfiniteReachable]
      exact p₀.reachable
    exact ⟨⟨x.1, hxmem⟩, z, hboundary, hconn⟩

theorem verticalRectangle_subset_bottom_oneArm_union (n : ℕ) :
    verticalRectangle (-(n : ℤ), 0) (2 * n) n ⊆
      ⋃ x : {z : ℤ // z ∈ Finset.Icc (-(n : ℤ)) n},
        oneArmBoundaryEvent (x.val, 0) n := by
  intro ω hω
  obtain ⟨x, hx⟩ := vertical_crossing_has_bottom_one_arm n ω hω
  exact Set.mem_iUnion.2 ⟨x, hx⟩

end PottsContinuity.Thm3.Easy
