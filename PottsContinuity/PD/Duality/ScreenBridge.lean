-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/ScreenBridge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Topology.Circle.Degree
public import PottsContinuity.PD.Duality.BondStates
public import PottsContinuity.PD.Defs.RCInfiniteOpenGraph
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! The copied whole-plane geometry uses the exact frozen open graph. -/

@[expose] public section

namespace PottsContinuity.PD.Duality

open FK FK.Medial

/-- Equality of the literal edge-state graph and the frozen open graph. -/
theorem wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph (ω : LatticeConfiguration) :
    wholePlaneOpenPrimalGraph ω = rcInfiniteOpenGraph ω := by
  ext u v
  rw [rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    exact ⟨⟨squareLattice.mem_edgeSet.mpr hadj, hopen⟩, hadj.ne⟩
  · rintro ⟨⟨he, hopen⟩, _⟩
    exact ⟨squareLattice.mem_edgeSet.mp he, hopen⟩

end PottsContinuity.PD.Duality
