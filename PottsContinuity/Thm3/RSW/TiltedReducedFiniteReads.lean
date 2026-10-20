module

public import PottsContinuity.Thm3.RSW.TiltedReducedFiniteDuality
public import PottsContinuity.Thm3.RSW.TiltedStripReducedDualCoordinates
public import PottsContinuity.DualityExt.PositiveSubgraphDualEdgeEquiv

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality DualityExt Thm3.Prop4
noncomputable section

/-- The actual finite dual edge crossed by a retained original source edge. -/
def tiltedReducedFiniteDualEdge (N M : ℕ) (t : ℝ)
    (e : (tiltedWindowReducedGraph N M t).edgeSet) :
    (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)).edgeSet :=
  rectangleSubgraphDualEdgeEmbedding (tiltedReducedHost_map_le N M t)
    (isolatedExtensionEdgeEquiv _ (tiltedReducedHostEmbedding N M t) e)

/-- Every retained original bond has exactly one actual retained dual bond. -/
def tiltedReducedFiniteEdgeEquiv (N M : ℕ) (t : ℝ) :
    (tiltedWindowReducedGraph N M t).edgeSet ≃
      (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)).edgeSet :=
  (isolatedExtensionEdgeEquiv _ (tiltedReducedHostEmbedding N M t)).trans
    (rectangleSubgraphDualEdgeEquiv (tiltedReducedHost_map_le N M t))

/-- The literal original bond represented by a retained source edge in the host. -/
def tiltedReducedFiniteSourceBond (N M : ℕ) (t : ℝ)
    (e : (tiltedWindowReducedGraph N M t).edgeSet) : LatticeBond :=
  rectanglePrimalEdgeBond (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2))
    (subgraphEdgeEmbedding (tiltedReducedHost_map_le N M t)
      (isolatedExtensionEdgeEquiv _ (tiltedReducedHostEmbedding N M t) e))

/-- The host original bond has exactly the source edge's physical endpoints. -/
theorem tiltedReducedFiniteSourceBond_pair (N M : ℕ) (t : ℝ)
    (e : (tiltedWindowReducedGraph N M t).edgeSet) :
    (tiltedReducedFiniteSourceBond N M t e).toSym2 =
      Sym2.map (fun z => z.val) e.val := by
  let g := subgraphEdgeEmbedding (tiltedReducedHost_map_le N M t)
    (isolatedExtensionEdgeEquiv _ (tiltedReducedHostEmbedding N M t) e)
  have h : latticeBondEdge (tiltedReducedFiniteSourceBond N M t e) =
      rectanglePrimalEdgeToSquareEdge (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) g :=
    wholePlaneBondEdgeEquiv.apply_symm_apply _
  have hp := congrArg Subtype.val h
  change (tiltedReducedFiniteSourceBond N M t e).toSym2 = Sym2.map Subtype.val g.val at hp
  dsimp [g] at hp
  change (tiltedReducedFiniteSourceBond N M t e).toSym2 =
    Sym2.map Subtype.val (Sym2.map (tiltedReducedHostEmbedding N M t) e.val) at hp
  rw [Sym2.map_map] at hp
  exact hp

/-- Every original retained source bit is complemented at its actual dual
edge, before any spatial reflection or probability comparison. -/
theorem tiltedReducedFiniteDualEquiv_edgeState (N M : ℕ) (t : ℝ)
    (C : Configuration (tiltedWindowReducedGraph N M t))
    (e : (tiltedWindowReducedGraph N M t).edgeSet) :
    tiltedReducedFiniteDualEdge N M t e ∈ tiltedReducedFiniteDualEquiv N M t C ↔ e ∉ C := by
  classical
  exact embeddedRectangleSubgraphDualConfiguration_edgeState (W := Unit)
    (tiltedReducedHostEmbedding N M t) (tiltedReducedHost_map_le N M t) C e

/-- After the genuine dual vertex half-turn the finite dual edge has
exactly the announced crossed original-bond endpoints. -/
theorem tiltedReducedFiniteDualEdge_crossed_pair (N M : ℕ) (t : ℝ)
    (e : (tiltedWindowReducedGraph N M t).edgeSet) :
    Sym2.map (fun z => tiltedStripReducedDualVertex N t z.val)
      (tiltedReducedFiniteDualEdge N M t e).val =
      (tiltedStripReducedCrossedBond N t (tiltedReducedFiniteSourceBond N M t e)).toSym2 := by
  change Sym2.map ((tiltedStripReducedDualVertex N t) ∘ Subtype.val)
    (rectangleSubgraphDualEdgeEmbedding (tiltedReducedHost_map_le N M t)
      (isolatedExtensionEdgeEquiv _ (tiltedReducedHostEmbedding N M t) e)).val = _
  rw [← Sym2.map_map,rectangleSubgraphDualEdgeEmbedding_crossingBond]
  exact tiltedStripReducedDualBond_dualBondOfPrimal_pair N t _

end
end PottsContinuity.RSW
