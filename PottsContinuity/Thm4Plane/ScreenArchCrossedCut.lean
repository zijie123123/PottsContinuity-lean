module

public import PottsContinuity.Thm4Plane.ScreenTargetExterior
public import PottsContinuity.Thm4Plane.ScreenCapResidualConfiguration

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC.Medial

noncomputable section

local instance screenArchCrossedCutEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

/-- The finite primal bonds crossed by edges of a chosen simple source-screen
dual arch. -/
def screenArchCrossedBondConfiguration (m : ℕ)
    (A : Configuration (slitBoxGraph (16 * m)))
    {lb rb : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb) :
    Configuration (slitBoxGraph (16 * m)) := by
  classical
  exact Finset.univ.filter fun e => ∃ d : LatticeBond,
    latticeBondEdge (primalBondOfDual d) = slitBoxEdgeEmbedding (16 * m) e ∧
      s(d.source, d.target) ∈ p.edges

/-- Every bond in the arch-crossed set is closed in its source configuration. -/
theorem screenArchCrossedBondConfiguration_mem_closed
    (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16 * m)))
    {lb rb : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb)
    (e : (slitBoxGraph (16 * m)).edgeSet)
    (he : e ∈ screenArchCrossedBondConfiguration m A p) : e ∉ A := by
  classical
  rcases Finset.mem_filter.mp he with ⟨_, d, hcross, hpathEdge⟩
  have hDualAdj : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Adj d.source d.target := by
    exact p.adj_of_mem_edges hpathEdge
  rcases generalScreenActualClosedDualGraph_adj_crossing_not_insideTargetBox
      m hm A hDualAdj with ⟨d', e', hcross', hclosed', hdir, _⟩
  have hdSym : d'.toSym2 = d.toSym2 := by
    rcases hdir with h | h
    · change s(d'.source, d'.target) = s(d.source, d.target)
      rw [h.1, h.2]
    · change s(d'.source, d'.target) = s(d.source, d.target)
      rw [h.1, h.2]
      exact Sym2.eq_swap
  have hd : d' = d := LatticeBond.toSym2_injective hdSym
  have hEmbed : slitBoxEdgeEmbedding (16 * m) e =
      slitBoxEdgeEmbedding (16 * m) e' := by
    calc
      slitBoxEdgeEmbedding (16 * m) e = latticeBondEdge (primalBondOfDual d) := hcross.symm
      _ = latticeBondEdge (primalBondOfDual d') := by rw [hd]
      _ = slitBoxEdgeEmbedding (16 * m) e' := hcross'
  have heq : e = e' := (slitBoxEdgeEmbedding (16 * m)).injective hEmbed
  rw [heq]
  exact hclosed'

private theorem crossedPrimalBond_in_targetBox_of_capInternalEdge
    (m : ℕ) (e : (slitBoxGraph (16 * m)).edgeSet) (d : LatticeBond)
    (hcross : latticeBondEdge (primalBondOfDual d) =
      slitBoxEdgeEmbedding (16 * m) e)
    (hInternal : screenTargetCapInternalEdge m e) :
    screenTargetPrimalBondInBox m (primalBondOfDual d) := by
  rcases hInternal with ⟨u, v, huv⟩
  have hval := congrArg Subtype.val hcross
  change s((primalBondOfDual d).source, (primalBondOfDual d).target) =
    Sym2.map Subtype.val e.val at hval
  rw [huv, Sym2.map_mk] at hval
  have hu := u.property
  have hv := v.property
  change -(m : ℤ) ≤ u.val.val.1 ∧ u.val.val.1 ≤ (m : ℤ) ∧
      -(16 * (m : ℤ)) ≤ u.val.val.2 ∧ u.val.val.2 ≤ -(15 * (m : ℤ)) at hu
  change -(m : ℤ) ≤ v.val.val.1 ∧ v.val.val.1 ≤ (m : ℤ) ∧
      -(16 * (m : ℤ)) ≤ v.val.val.2 ∧ v.val.val.2 ≤ -(15 * (m : ℤ)) at hv
  change -(m : ℤ) ≤ (primalBondOfDual d).source.1 ∧
    (primalBondOfDual d).target.1 ≤ (m : ℤ) ∧
    -(17 * (m : ℤ)) ≤ (primalBondOfDual d).source.2 ∧
    (primalBondOfDual d).target.2 ≤ -(15 * (m : ℤ))
  unfold LatticeBond.source LatticeBond.target at *
  rcases Sym2.eq_iff.mp hval with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [ht, hs]
    omega
  · rw [ht, hs]
    omega

/-- If the support of the chosen arch lies outside the target box, no bond it
crosses can be internal to the retained target cap. -/
theorem screenArchCrossedBondConfiguration_avoids_capInternalEdge_of_exteriorSupport
    (m : ℕ) (A : Configuration (slitBoxGraph (16 * m)))
    {lb rb : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb)
    (hExterior : ∀ z ∈ p.support,
      2 * z.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * z.1 + 1 ∨
          -(30 * (m : ℤ)) < 2 * z.2 + 1) :
    ∀ e ∈ screenArchCrossedBondConfiguration m A p,
      ¬ screenTargetCapInternalEdge m e := by
  classical
  intro e he hInternal
  rcases Finset.mem_filter.mp he with ⟨_, d, hcross, hpathEdge⟩
  have hsource : d.source ∈ p.support :=
    p.fst_mem_support_of_mem_edges hpathEdge
  have htarget : d.target ∈ p.support :=
    p.snd_mem_support_of_mem_edges hpathEdge
  have hnotbox : ¬ screenTargetPrimalBondInBox m (primalBondOfDual d) :=
    dualBond_crossingBond_not_in_target_of_faceCenters_outside m d
      (hExterior d.source hsource) (hExterior d.target htarget)
  exact hnotbox
    (crossedPrimalBond_in_targetBox_of_capInternalEdge m e d hcross hInternal)

end

end PottsContinuity.Thm4Plane
