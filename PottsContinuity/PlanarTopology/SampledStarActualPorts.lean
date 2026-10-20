module

public import PottsContinuity.PlanarTopology.SampledClosedRowsScreen
public import PottsContinuity.PlanarTopology.FourCyclePorts
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial

/-- Actual incident face ports form one connected set as soon as one genuine
horizontal and one genuine vertical star bond are closed. Missing outside
bonds and their isolated corner faces are never inserted. -/
theorem rectangle_sampled_star_actual_ports_connected
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h)) (z : LatticeVertex)
    (hHorizontal : rectangleSampledBondClosed a w h A ⟨z,.horizontal⟩ ∨
      rectangleSampledBondClosed a w h A ⟨(z.1-1,z.2),.horizontal⟩)
    (hVertical : rectangleSampledBondClosed a w h A ⟨z,.vertical⟩ ∨
      rectangleSampledBondClosed a w h A ⟨(z.1,z.2-1),.vertical⟩)
    (f g : LatticeVertex)
    (hf : fourCyclePort (rectangleSampledClosedDualGraph a w h A)
      (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) f)
    (hg : fourCyclePort (rectangleSampledClosedDualGraph a w h A)
      (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) g) :
    (rectangleSampledClosedDualGraph a w h A).Reachable f g := by
  let G := rectangleSampledClosedDualGraph a w h A
  have hE (he : rectangleSampledBondClosed a w h A ⟨z,.horizontal⟩) :
      G.Adj (z.1,z.2-1) z := sampled_closed_horizontal_row_dual_adj a w h A z.1 z.2 he
  have hW (hw : rectangleSampledBondClosed a w h A ⟨(z.1-1,z.2),.horizontal⟩) :
      G.Adj (z.1-1,z.2-1) (z.1-1,z.2) :=
    sampled_closed_horizontal_row_dual_adj a w h A (z.1-1) z.2 hw
  have hN (hn : rectangleSampledBondClosed a w h A ⟨z,.vertical⟩) :
      G.Adj (z.1-1,z.2) z := sampled_closed_vertical_column_dual_adj a w h A z.1 z.2 hn
  have hS (hs : rectangleSampledBondClosed a w h A ⟨(z.1,z.2-1),.vertical⟩) :
      G.Adj (z.1-1,z.2-1) (z.1,z.2-1) :=
    sampled_closed_vertical_column_dual_adj a w h A z.1 (z.2-1) hs
  change fourCyclePort G (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) f at hf
  change fourCyclePort G (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) g at hg
  have rot1 (x : LatticeVertex) (hx : fourCyclePort G
      (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) x) :=
    (fourCyclePort_cyclic G (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) x).mpr hx
  have rot2 (x : LatticeVertex) (hx : fourCyclePort G
      (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) x) :=
    (fourCyclePort_cyclic G (z.1,z.2-1) z (z.1-1,z.2) (z.1-1,z.2-1) x).mpr (rot1 x hx)
  have rot3 (x : LatticeVertex) (hx : fourCyclePort G
      (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2) x) :=
    (fourCyclePort_cyclic G z (z.1-1,z.2) (z.1-1,z.2-1) (z.1,z.2-1) x).mpr (rot2 x hx)
  rcases hHorizontal with he | hw <;> rcases hVertical with hn | hs
  · exact fourCycle_ports_connected_of_adjacent G (z.1,z.2-1) z (z.1-1,z.2) (z.1-1,z.2-1)
      (hE he) (hN hn).symm f g
      (rot1 f hf) (rot1 g hg)
  · exact fourCycle_ports_connected_of_adjacent G (z.1-1,z.2-1) (z.1,z.2-1) z (z.1-1,z.2)
      (hS hs) (hE he) f g hf hg
  · exact fourCycle_ports_connected_of_adjacent G z (z.1-1,z.2) (z.1-1,z.2-1) (z.1,z.2-1)
      (hN hn).symm (hW hw).symm f g
      (rot2 f hf) (rot2 g hg)
  · exact fourCycle_ports_connected_of_adjacent G (z.1-1,z.2) (z.1-1,z.2-1) (z.1,z.2-1) z
      (hW hw).symm (hS hs) f g
      (rot3 f hf) (rot3 g hg)

end PottsContinuity.PlanarTopology
