-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedClosedCap.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedDirectEdges
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis

/-- The midpoint in the refined grid between a port on the radius-four layer
and its deterministic closed pair on that same layer. -/
def parafermionicCoverRefinedClosedCapMiddle
    (c : ParafermionicCoverPort) : ParafermionicCoverVertex :=
  let u := parafermionicCoverRefinedPortEmbedding (c, false)
  let v := parafermionicCoverRefinedPortEmbedding
    (parafermionicCoverClosedPair c, false)
  (((u.1.1 + v.1.1) / 2, (u.1.2 + v.1.2) / 2), c.2)

@[simp] theorem parafermionicCoverRefinedClosedCapMiddle_sheet
    (c : ParafermionicCoverPort) :
    (parafermionicCoverRefinedClosedCapMiddle c).2 = c.2 := rfl

theorem parafermionicCoverRefinedClosedCapMiddle_horizontal
    (x y : ℤ) (tip side : Bool) (k : ℤ) :
    parafermionicCoverRefinedClosedCapMiddle
      ((⟨⟨(x, y), horizontal⟩, tip, side⟩ : LatticePort), k) =
      ((9 * x + (if tip then (1 : ℤ) else 0), 9 * y + 4), k) := by
  cases tip <;> cases side <;>
    simp [parafermionicCoverRefinedClosedCapMiddle,
      parafermionicCoverClosedPair, LatticePort.closedPair,
      parafermionicCoverRefinedPortEmbedding_horizontal] <;> omega

theorem parafermionicCoverRefinedClosedCapMiddle_vertical
    (x y : ℤ) (tip side : Bool) (k : ℤ) :
    parafermionicCoverRefinedClosedCapMiddle
      ((⟨⟨(x, y), vertical⟩, tip, side⟩ : LatticePort), k) =
      ((9 * x - 4, 9 * y + 8 + (if tip then (1 : ℤ) else 0)), k) := by
  cases tip <;> cases side <;>
    simp [parafermionicCoverRefinedClosedCapMiddle,
      parafermionicCoverClosedPair, LatticePort.closedPair,
      parafermionicCoverRefinedPortEmbedding_vertical] <;> omega

theorem parafermionicCoverRefinedClosedCapMiddle_closedPair
    (c : ParafermionicCoverPort) :
    parafermionicCoverRefinedClosedCapMiddle (parafermionicCoverClosedPair c) =
      parafermionicCoverRefinedClosedCapMiddle c := by
  rcases c with ⟨p, k⟩
  rcases p with ⟨⟨base, ax⟩, tip, side⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverRefinedClosedCapMiddle,
      parafermionicCoverClosedPair, LatticePort.closedPair,

      ]<;> omega

theorem parafermionicCoverRefinedClosedCapMiddle_base_adj
    (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Adj
      (parafermionicCoverRefinedPortEmbedding (c, false))
      (parafermionicCoverRefinedClosedCapMiddle c) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax
  · rw [parafermionicCoverRefinedPortEmbedding_horizontal x y tip side false k,
      parafermionicCoverRefinedClosedCapMiddle_horizontal x y tip side k]
    cases tip <;> cases side <;>
      rw [parafermionicCoverGraph_adj_iff_cases] <;>
      simp [parafermionicCoverAdjCases] <;> omega
  · rw [parafermionicCoverRefinedPortEmbedding_vertical x y tip side false k,
      parafermionicCoverRefinedClosedCapMiddle_vertical x y tip side k]
    cases tip <;> cases side <;>
      rw [parafermionicCoverGraph_adj_iff_cases] <;>
      simp [parafermionicCoverAdjCases] <;> omega

theorem parafermionicCoverRefinedClosedCapMiddle_closedPair_adj
    (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Adj
      (parafermionicCoverRefinedClosedCapMiddle c)
      (parafermionicCoverRefinedPortEmbedding
        (parafermionicCoverClosedPair c, false)) := by
  have h := parafermionicCoverRefinedClosedCapMiddle_base_adj
    (parafermionicCoverClosedPair c)
  rw [parafermionicCoverRefinedClosedCapMiddle_closedPair] at h
  exact h.symm

theorem parafermionicCoverRefinedClosedCapMiddle_ne_embedding
    (c d : ParafermionicCoverPort) (layer : Bool) :
    parafermionicCoverRefinedClosedCapMiddle c ≠
      parafermionicCoverRefinedPortEmbedding (d, layer) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  intro h
  cases ax <;> cases axp <;> cases tip <;> cases side <;>
    cases tipp <;> cases sidep <;> cases layer <;>
    simp [parafermionicCoverRefinedClosedCapMiddle,
      parafermionicCoverClosedPair, LatticePort.closedPair,

      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical] at h <;> omega

end PottsContinuity.FKC.Medial
