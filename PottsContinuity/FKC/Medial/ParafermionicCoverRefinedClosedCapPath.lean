-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedClosedCapPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCap
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedDirectEdges
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

/-- The literal two-edge refined-grid route across the closed cap of a lifted
port: the radius-four port, its midpoint, and the closed-paired port. -/
def parafermionicCoverRefinedClosedCapWalk (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Walk
      (parafermionicCoverRefinedPortEmbedding (c, false))
      (parafermionicCoverRefinedPortEmbedding (parafermionicCoverClosedPair c, false)) :=
  Walk.cons (parafermionicCoverRefinedClosedCapMiddle_base_adj c)
    (Walk.cons (parafermionicCoverRefinedClosedCapMiddle_closedPair_adj c) Walk.nil)

@[simp] theorem parafermionicCoverRefinedClosedCapWalk_support
    (c : ParafermionicCoverPort) :
    (parafermionicCoverRefinedClosedCapWalk c).support =
      [parafermionicCoverRefinedPortEmbedding (c, false),
       parafermionicCoverRefinedClosedCapMiddle c,
       parafermionicCoverRefinedPortEmbedding (parafermionicCoverClosedPair c, false)] := by
  simp [parafermionicCoverRefinedClosedCapWalk]

@[simp] theorem parafermionicCoverRefinedClosedCapWalk_length
    (c : ParafermionicCoverPort) :
    (parafermionicCoverRefinedClosedCapWalk c).length = 2 := by
  simp [parafermionicCoverRefinedClosedCapWalk]

theorem parafermionicCoverRefinedClosedCapWalk_isPath
    (c : ParafermionicCoverPort) :
    (parafermionicCoverRefinedClosedCapWalk c).IsPath := by
  apply Walk.IsPath.mk'
  rw [parafermionicCoverRefinedClosedCapWalk_support]
  have hbase : parafermionicCoverRefinedPortEmbedding (c, false) ≠
      parafermionicCoverRefinedPortEmbedding (parafermionicCoverClosedPair c, false) := by
    intro h
    have hpair : (c, false) = (parafermionicCoverClosedPair c, false) :=
      parafermionicCoverRefinedPortEmbedding_injective h
    have : c = parafermionicCoverClosedPair c := congrArg Prod.fst hpair
    exact (parafermionicCoverClosedPair_ne c).symm this
  apply List.nodup_cons.mpr
  constructor
  · intro h
    simp only [List.mem_cons, List.not_mem_nil] at h
    rcases h with h | h
    · exact (parafermionicCoverRefinedClosedCapMiddle_ne_embedding c c false).symm h
    · rcases h with h | h
      · exact hbase h
      · contradiction
  · apply List.nodup_cons.mpr
    constructor
    · intro h
      simp only [List.mem_cons, List.not_mem_nil] at h
      rcases h with h | h
      · exact parafermionicCoverRefinedClosedCapMiddle_ne_embedding c
          (parafermionicCoverClosedPair c) false h
      · contradiction
    · simp

theorem parafermionicCoverRefinedClosedCapMiddle_eq_iff
    (c d : ParafermionicCoverPort) :
    parafermionicCoverRefinedClosedCapMiddle c =
      parafermionicCoverRefinedClosedCapMiddle d ↔
        d = c ∨ d = parafermionicCoverClosedPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨x', y'⟩, ax'⟩, tip', side'⟩, k'⟩
  cases ax <;> cases ax' <;> cases tip <;> cases tip' <;>
    cases side <;> cases side' <;>
    simp [parafermionicCoverRefinedClosedCapMiddle_horizontal,
      parafermionicCoverRefinedClosedCapMiddle_vertical,
      parafermionicCoverClosedPair, LatticePort.closedPair] <;> omega

end PottsContinuity.FKC.Medial
