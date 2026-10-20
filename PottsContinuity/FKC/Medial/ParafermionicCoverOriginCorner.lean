-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverOriginCorner.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPorts
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverOriginInterior
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis LatticeBond LatticePort

/-- A literal lifted medial-port occurrence at the upper-left primal corner of the
unit face below the origin. -/
def parafermionicCoverOriginCornerPort : ParafermionicCoverPort :=
  (⟨⟨(0,0), horizontal⟩, false, false⟩, 0)

/-- The other literal lifted port occurrence at that same primal corner and face. -/
def parafermionicCoverOriginCornerPortOther : ParafermionicCoverPort :=
  parafermionicCoverCornerPair parafermionicCoverOriginCornerPort

theorem parafermionicCoverOriginCornerPort_primalVertex :
    parafermionicCoverPortVertex parafermionicCoverOriginCornerPort = ((0,0),0) := by
  rfl

theorem parafermionicCoverOriginCornerPortOther_primalVertex :
    parafermionicCoverPortVertex parafermionicCoverOriginCornerPortOther = ((0,0),0) := by
  rw [parafermionicCoverOriginCornerPortOther,
    parafermionicCoverCornerPair_vertex,
    parafermionicCoverOriginCornerPort_primalVertex]

theorem parafermionicCoverOriginCornerPorts_ne :
    parafermionicCoverOriginCornerPortOther ≠ parafermionicCoverOriginCornerPort := by
  intro h
  exact cornerPair_ne parafermionicCoverOriginCornerPort.1 (congrArg Prod.fst h)

private theorem parafermionicCoverOriginCornerPort_other_adjacent
    (c : ParafermionicCoverPort)
    (hc : c = parafermionicCoverOriginCornerPort ∨
      c = parafermionicCoverOriginCornerPortOther) :
    parafermionicCoverGraph.Adj (parafermionicCoverPortVertex c)
      (parafermionicCoverPortOtherVertex c) := by
  rcases hc with rfl | rfl
  · rw [parafermionicCoverPortOtherVertex_eq_neighborLift]
    change parafermionicCoverGraph.Adj ((0,0),0)
      (parafermionicCoverNeighborLift ((0,0),0) (1,0))
    apply parafermionicCoverNeighborLift_adj
    simp [squareLattice]
  · rw [parafermionicCoverPortOtherVertex_eq_neighborLift]
    change parafermionicCoverGraph.Adj ((0,0),0)
      (parafermionicCoverNeighborLift ((0,0),0) (0,-1))
    apply parafermionicCoverNeighborLift_adj
    simp [squareLattice]

private theorem parafermionicCoverOrigin_mem_box (n : ℕ) (hn : 1 ≤ n) :
    ((0,0),0) ∈ parafermionicCoverBoxVertices n := by
  rw [parafermionicCoverBoxVertices_mem]
  have hnZ : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  norm_num

theorem parafermionicCoverOriginCornerPort_edge_endpoints_in_box
    (n : ℕ) (hn : 1 ≤ n)
    (c : ParafermionicCoverPort)
    (hc : c = parafermionicCoverOriginCornerPort ∨
      c = parafermionicCoverOriginCornerPortOther) :
    ∀ v ∈ (parafermionicCoverPortEdge c).1, v ∈ parafermionicCoverBoxVertices n := by
  intro v hv
  rw [parafermionicCoverPortEdge_eq_incident_pair] at hv
  rcases (Sym2.mem_iff').mp hv with hv | hv
  · rw [hv]
    rcases hc with rfl | rfl
    · exact parafermionicCoverOrigin_mem_box n hn
    · rw [parafermionicCoverOriginCornerPortOther_primalVertex]
      exact parafermionicCoverOrigin_mem_box n hn
  · rw [hv]
    rcases hc with rfl | rfl
    · apply parafermionicCoverBoxOrigin_neighbor_mem_box n hn
      exact parafermionicCoverOriginCornerPort_other_adjacent _ (Or.inl rfl)
    · apply parafermionicCoverBoxOrigin_neighbor_mem_box n hn
      exact parafermionicCoverOriginCornerPort_other_adjacent _ (Or.inr rfl)

end PottsContinuity.FKC.Medial
