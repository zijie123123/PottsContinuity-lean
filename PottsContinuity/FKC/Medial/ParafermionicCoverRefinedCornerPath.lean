-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedCornerPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCap
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis

/-- Close a disjunction by trying `omega` on one disjunct at a time, so `omega`
does not case-split the whole disjunction at once. -/
local syntax "disj_omega" : tactic
local macro_rules
  | `(tactic| disj_omega) => `(tactic| first | (left; omega) | (right; disj_omega) | omega)

/-- The middle elbow of the four-edge fine-grid route between a port and its
corner pair. -/
def parafermionicCoverRefinedCornerElbow (c : ParafermionicCoverPort) : ParafermionicCoverVertex :=
  let u := parafermionicCoverRefinedPortEmbedding (c, true)
  let v := parafermionicCoverRefinedPortEmbedding (parafermionicCoverCornerPair c, true)
  match c.1.bond.axis with
  | horizontal => ((v.1.1, u.1.2), c.2)
  | vertical => ((u.1.1, v.1.2), c.2)

/-- First midpoint on the route from the refined port to its elbow. -/
def parafermionicCoverRefinedCornerMid₁ (c : ParafermionicCoverPort) : ParafermionicCoverVertex :=
  let u := parafermionicCoverRefinedPortEmbedding (c, true)
  let e := parafermionicCoverRefinedCornerElbow c
  (((u.1.1 + e.1.1) / 2, (u.1.2 + e.1.2) / 2), c.2)

/-- Second midpoint on the route from the elbow to the refined corner pair. -/
def parafermionicCoverRefinedCornerMid₂ (c : ParafermionicCoverPort) : ParafermionicCoverVertex :=
  let e := parafermionicCoverRefinedCornerElbow c
  let v := parafermionicCoverRefinedPortEmbedding (parafermionicCoverCornerPair c, true)
  (((e.1.1 + v.1.1) / 2, (e.1.2 + v.1.2) / 2), c.2)

theorem parafermionicCoverRefinedCornerRoute_adj
    (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Adj (parafermionicCoverRefinedPortEmbedding (c, true))
      (parafermionicCoverRefinedCornerMid₁ c) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverRefinedCornerMid₁ c)
      (parafermionicCoverRefinedCornerElbow c) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverRefinedCornerElbow c)
      (parafermionicCoverRefinedCornerMid₂ c) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverRefinedCornerMid₂ c)
      (parafermionicCoverRefinedPortEmbedding (parafermionicCoverCornerPair c, true)) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerMid₂,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverCornerPair, parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical, LatticePort.cornerPair,


      parafermionicCoverGraph_adj_iff_cases, parafermionicCoverAdjCases] <;>
    and_intros <;> disj_omega

def parafermionicCoverRefinedCornerWalk (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Walk
      (parafermionicCoverRefinedPortEmbedding (c, true))
      (parafermionicCoverRefinedPortEmbedding (parafermionicCoverCornerPair c, true)) := by
  let h := parafermionicCoverRefinedCornerRoute_adj c
  exact SimpleGraph.Walk.cons h.1 (SimpleGraph.Walk.cons h.2.1
    (SimpleGraph.Walk.cons h.2.2.1
      (SimpleGraph.Walk.cons h.2.2.2 SimpleGraph.Walk.nil)))

@[simp] theorem parafermionicCoverRefinedCornerWalk_length
    (c : ParafermionicCoverPort) :
    (parafermionicCoverRefinedCornerWalk c).length = 4 := by
  simp [parafermionicCoverRefinedCornerWalk]

@[simp] theorem parafermionicCoverRefinedCornerWalk_support
    (c : ParafermionicCoverPort) :
    (parafermionicCoverRefinedCornerWalk c).support =
      [parafermionicCoverRefinedPortEmbedding (c, true),
       parafermionicCoverRefinedCornerMid₁ c,
       parafermionicCoverRefinedCornerElbow c,
       parafermionicCoverRefinedCornerMid₂ c,
       parafermionicCoverRefinedPortEmbedding (parafermionicCoverCornerPair c, true)] := by
  simp [parafermionicCoverRefinedCornerWalk]


theorem parafermionicCoverRefinedCornerWalk_isPath
    (c : ParafermionicCoverPort) :
    (parafermionicCoverRefinedCornerWalk c).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,
    parafermionicCoverRefinedCornerWalk_support]
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [
      parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerMid₂,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverCornerPair, parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical, LatticePort.cornerPair,

      List.nodup_cons] <;> omega

end PottsContinuity.FKC.Medial
