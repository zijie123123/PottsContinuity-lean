module

public import PottsContinuity.Thm3.RSW.FiniteDualClosure
public import PottsContinuity.Thm3.Prop4.SquareEscape

/-! # Actual finite closed-dual walks on the face-base lattice -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

/-- The identity on face bases embeds the actual sampled closed-dual graph
of the closed extension into the nearest-neighbour lattice. -/
def finiteClosedDualLatticeHom (V : Finset LatticeVertex)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex))) :
    wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A) →g PD.FK.squareLattice where
  toFun := id
  map_rel' := by
    intro u v h
    exact Thm3.Prop4.wholePlaneClosedDualGraph_le_squareLattice _ h

/-- Every walk in the actual closed-dual graph satisfies the exact sampled
finite closure predicate after its identity embedding into the lattice. -/
theorem finiteDualWalkClosed_of_closedDualWalk (V : Finset LatticeVertex)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    {z : LatticeVertex}
    (p : (wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A)).Walk z z) :
    finiteDualWalkClosed V A (p.map (finiteClosedDualLatticeHom V A)) := by
  rw [finiteDualWalkClosed_iff_closedExtension_dualAdj]
  intro u v he
  rw [SimpleGraph.Walk.edges_map] at he
  change s(u,v) ∈ p.edges.map (Sym2.map id) at he
  simpa only [Sym2.map_id,List.map_id] using p.adj_of_mem_edges (by
    simpa only [Sym2.map_id,List.map_id] using he)

end PottsContinuity.RSW
