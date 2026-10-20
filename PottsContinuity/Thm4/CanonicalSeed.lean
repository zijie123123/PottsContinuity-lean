module

public import PottsContinuity.Thm4.EdgeCutTerminals

/-!
# Canonical seed for a queried edge

The incoming source-tip port is uniquely determined by its actual lifted edge.
This removes the non-unique seed choice used by the upstream terminal labeling.
-/

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

def sourceIncomingPort (c : ParafermionicCoverPort) : ParafermionicCoverPort :=
  (⟨c.1.bond, false, match c.1.bond.axis with
    | .horizontal => false
    | .vertical => true⟩, parafermionicCoverPortSourceSheet c)

private theorem sourceIncomingPort_edge (c : ParafermionicCoverPort) :
    parafermionicCoverPortEdge (sourceIncomingPort c) = parafermionicCoverPortEdge c := by
  apply Subtype.ext
  simp only [parafermionicCoverPortEdge_val]
  rfl

/-- Each finite edge has a unique source-tip port with incoming primal-left flag. -/
theorem canonicalIncomingPort_existsUnique (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ∃! c : ParafermionicCoverFinitePort n,
      parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
        c.1.1.tip = false ∧ parafermionicCoverIncomingPrimalLeft c.1 = true := by
  obtain ⟨c, hc⟩ := parafermionicCoverPort_exists_for_edge
    (parafermionicCoverFiniteEdgeEmbedding n e)
  have hedge := (sourceIncomingPort_edge c).trans hc
  have hmem : parafermionicCoverPortVertex (sourceIncomingPort c) ∈
      parafermionicCoverBoxVertices n := by
    apply parafermionicCoverFiniteEdgeEmbedding_endpoints_mem n e
    rw [← hedge, parafermionicCoverPortEdge_eq_incident_pair]
    exact Sym2.mem_mk_left _ _
  let seed : ParafermionicCoverFinitePort n := ⟨sourceIncomingPort c, hmem⟩
  have htip : seed.1.1.tip = false := rfl
  have hflag : parafermionicCoverIncomingPrimalLeft seed.1 = true := by
    cases hax : c.1.bond.axis <;>
      simp [seed, sourceIncomingPort, parafermionicCoverIncomingPrimalLeft,
        medialIncomingPrimalLeft, hax]
  refine ⟨seed, ⟨hedge, htip, hflag⟩, ?_⟩
  intro d hd
  have hedges : parafermionicCoverPortEdge d.1 = parafermionicCoverPortEdge seed.1 :=
    hd.1.trans hedge.symm
  rcases (parafermionicCoverPortEdge_eq_iff_four seed.1 d.1).1 hedges with h | h | h | h
  · exact Subtype.ext h
  · have ht := hd.2.1
    rw [h] at ht
    simp [parafermionicCoverOpenPair, LatticePort.openPair, htip] at ht
  · have hf := hd.2.2
    rw [h, parafermionicCoverIncomingPrimalLeft_closedPair, hflag] at hf
    cases hf
  · have ht := hd.2.1
    rw [h] at ht
    simp [parafermionicCoverOpenPair, parafermionicCoverClosedPair,
      LatticePort.openPair, LatticePort.closedPair, htip] at ht

/-- The uniquely characterized incoming port at the source tip of an actual edge. -/
def canonicalIncomingPort (n : ℕ) (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFinitePort n :=
  Classical.choose (canonicalIncomingPort_existsUnique n e)

theorem canonicalIncomingPort_spec (n : ℕ) (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverPortEdge (canonicalIncomingPort n e).1 =
        parafermionicCoverFiniteEdgeEmbedding n e ∧
      (canonicalIncomingPort n e).1.1.tip = false ∧
      parafermionicCoverIncomingPrimalLeft (canonicalIncomingPort n e).1 = true :=
  (Classical.choose_spec (canonicalIncomingPort_existsUnique n e)).1

end
end PottsContinuity.Thm4
