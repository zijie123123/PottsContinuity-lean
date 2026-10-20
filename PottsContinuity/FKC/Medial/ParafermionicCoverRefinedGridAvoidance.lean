-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedGridAvoidance.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPortEmbedding
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerInterior
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- Actual refined port embeddings avoid the two residue classes of the
coarse routed grid. -/
theorem parafermionicCoverRefinedPortEmbedding_avoidsGridResidues
    (c : ParafermionicCoverPort) (layer : Bool) :
    let z := parafermionicCoverRefinedPortEmbedding (c, layer)
    z.1.1 % 9 ≠ 5 ∧ z.1.2 % 9 ≠ 4 := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;> cases layer <;>
    simp [parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical] <;> omega

/-- Every vertex in the actual strict interior of a corner route avoids the
coarse routed grid residues. -/
theorem parafermionicCoverRefinedCornerWalkInterior_avoidsGridResidues
    (c : ParafermionicCoverPort) {z : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverRefinedCornerWalkInterior c) :
    z.1.1 % 9 ≠ 5 ∧ z.1.2 % 9 ≠ 4 := by
  rw [parafermionicCoverRefinedCornerWalkInterior_eq] at hz
  simp only [List.mem_cons, List.not_mem_nil] at hz
  rcases hz with rfl | rfl | rfl | hfalse
  all_goals try contradiction
  all_goals
    rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCornerMid₁,
        parafermionicCoverRefinedCornerMid₂,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverCornerPair,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        LatticePort.cornerPair,
        ] <;> omega

/-- A point on either coarse-grid residue line cannot be an actual encoded
port at either layer. -/
theorem parafermionicCoverRefinedGridPoint_ne_portEmbedding
    {z : ParafermionicCoverVertex}
    (hgrid : z.1.1 % 9 = 5 ∨ z.1.2 % 9 = 4)
    (c : ParafermionicCoverPort) (layer : Bool) :
    z ≠ parafermionicCoverRefinedPortEmbedding (c, layer) := by
  intro h
  have hres := parafermionicCoverRefinedPortEmbedding_avoidsGridResidues c layer
  rcases hgrid with hx | hy
  · have hx' := congrArg (fun w : ParafermionicCoverVertex => w.1.1 % 9) h
    exact hres.1 (by simpa [hx'] using hx)
  · have hy' := congrArg (fun w : ParafermionicCoverVertex => w.1.2 % 9) h
    exact hres.2 (by simpa [hy'] using hy)

/-- A point on either coarse-grid residue line cannot lie in an actual corner
route's strict interior. -/
theorem parafermionicCoverRefinedGridPoint_not_mem_cornerWalkInterior
    {z : ParafermionicCoverVertex}
    (hgrid : z.1.1 % 9 = 5 ∨ z.1.2 % 9 = 4)
    (c : ParafermionicCoverPort) :
    z ∉ parafermionicCoverRefinedCornerWalkInterior c := by
  intro hz
  have hres := parafermionicCoverRefinedCornerWalkInterior_avoidsGridResidues c hz
  rcases hgrid with hx | hy
  · exact hres.1 hx
  · exact hres.2 hy

end PottsContinuity.FKC.Medial
