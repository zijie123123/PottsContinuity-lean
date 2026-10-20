module

public import PottsContinuity.PlanarTopology.KSTRectangleRealization
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite BD12
noncomputable section

/-- Forgetting sampled states preserves every original lattice adjacency. -/
theorem rcOpenGraph_le_squareLattice (ω : LatticeConfiguration) :
    PD.rcInfiniteOpenGraph ω ≤ PD.squareLattice := by
  intro u v huv
  exact PD.squareLattice.mem_edgeSet.mp ((rcInfiniteOpenGraph_adj ω u v).mp huv).1

/-- The ordinary lattice embedding of an actual sampled open walk keeps
all original open edge states, including at its two endpoints. -/
theorem kstPathOpen_of_rcOpen_walk (ω : LatticeConfiguration)
    {u v : LatticeVertex} (p : (PD.rcInfiniteOpenGraph ω).Walk u v) :
    kstPathOpen ω (p.mapLe (rcOpenGraph_le_squareLattice ω)) := by
  intro e he
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he
  rcases e with ⟨e,heG⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    exact ((rcInfiniteOpenGraph_adj ω x y).mp (p.adj_of_mem_edges he)).2

end
end PottsContinuity.PlanarTopology
