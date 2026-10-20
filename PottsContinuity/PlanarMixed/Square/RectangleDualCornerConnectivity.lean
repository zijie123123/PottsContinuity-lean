/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDualCornerConnectivity.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDualCornerClamp
public import PottsContinuity.PlanarMixed.Square.RectangleDualHorizontalCoreLaw
public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import PottsContinuity.PD.Duality.CrossingDuality
public import PottsContinuity.PD.Duality.RectangleEvents
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

/-- A dual edge either collapses under the corner clamp or remains an actual
open edge of the restricted corner graph. -/
theorem rectangleDualCornerClamp_openAdj
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    {u v : RectangleDualVertex a w h}
    (hadj : (openGraph (rectangleDualGraph a w h) A).Adj u v) :
    rectangleDualCornerClamp a w h u = rectangleDualCornerClamp a w h v ∨
      (openGraph (rectangleDualCornerCoreGraph a w h)
        (rectangleDualCornerCoreConfigurationRestriction a w h A)).Adj
        (rectangleDualCornerClamp a w h u) (rectangleDualCornerClamp a w h v) := by
  classical
  by_cases hout : ¬ (a.1 ≤ u.1.1 ∧ a.2 ≤ u.1.2) ∨
      ¬ (a.1 ≤ v.1.1 ∧ a.2 ≤ v.1.2)
  · exact Or.inl
      (rectangleDualCornerClamp_eq_of_adj_endpoint_outside a w h u v
        ((openGraph_le _ A) hadj) hout)
  · have hu : a.1 ≤ u.1.1 ∧ a.2 ≤ u.1.2 := by
      by_contra hn
      exact hout (Or.inl hn)
    have hv : a.1 ≤ v.1.1 ∧ a.2 ≤ v.1.2 := by
      by_contra hn
      exact hout (Or.inr hn)
    let cu := rectangleDualCornerClamp a w h u
    let cv := rectangleDualCornerClamp a w h v
    have hcu : rectangleDualCornerCoreEmbedding a w h cu = u :=
      rectangleDualCornerClamp_embedding_of_mem_corner a w h u hu.1 hu.2
    have hcv : rectangleDualCornerCoreEmbedding a w h cv = v :=
      rectangleDualCornerClamp_embedding_of_mem_corner a w h v hv.1 hv.2
    have hgraph : (rectangleDualCornerCoreGraph a w h).Adj cu cv := by
      change (rectangleDualGraph a w h).Adj
        (rectangleDualCornerCoreEmbedding a w h cu)
        (rectangleDualCornerCoreEmbedding a w h cv)
      simpa [hcu, hcv] using (openGraph_le _ A) hadj
    have hpairOpen : s(u, v) ∈ openEdges (rectangleDualGraph a w h) A :=
      (openGraph_adj _ _ _ _).mp hadj
    rcases hpairOpen with ⟨eH, heA, heval⟩
    let eC : (rectangleDualCornerCoreGraph a w h).edgeSet :=
      ⟨s(cu, cv), (rectangleDualCornerCoreGraph a w h).mem_edgeSet.mpr hgraph⟩
    have hEmbed : embeddedEdgeEmbedding (rectangleDualCornerCoreGraph a w h)
        (rectangleDualGraph a w h) (rectangleDualCornerCoreEmbedding a w h)
        (rectangleDualCornerCoreGraph_map_le_dual a w h) eC = eH := by
      apply Subtype.ext
      rw [embeddedEdgeEmbedding_coe]
      change Sym2.map (rectangleDualCornerCoreEmbedding a w h) (s(cu, cv)) = eH.val
      simp only [Sym2.map_mk]
      rw [hcu, hcv]
      exact heval.symm
    have heC : eC ∈ rectangleDualCornerCoreConfigurationRestriction a w h A :=
      (mem_rectangleDualCornerCoreConfigurationRestriction a w h A eC).2
        (hEmbed ▸ heA)
    have hOpenC : eC.val ∈ openEdges (rectangleDualCornerCoreGraph a w h)
        (rectangleDualCornerCoreConfigurationRestriction a w h A) :=
      (coe_mem_openEdges_iff _ _ _).2 heC
    have hadjC : (openGraph (rectangleDualCornerCoreGraph a w h)
        (rectangleDualCornerCoreConfigurationRestriction a w h A)).Adj cu cv := by
      rw [openGraph_adj]
      simpa [eC] using hOpenC
    exact Or.inr (by simpa [cu, cv] using hadjC)

/-- Clamping an actual open dual walk gives actual connectivity in the corner
restriction; every step either collapses or remains open. -/
theorem rectangleDualCornerClamp_actualConnected
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    {u v : RectangleDualVertex a w h}
    (hconn : ActualConnected (rectangleDualGraph a w h) A u v) :
    ActualConnected (rectangleDualCornerCoreGraph a w h)
      (rectangleDualCornerCoreConfigurationRestriction a w h A)
      (rectangleDualCornerClamp a w h u) (rectangleDualCornerClamp a w h v) := by
  obtain ⟨p⟩ := (actualConnected_iff_walk _ _ _ _).mp hconn
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hadj tail ih =>
      rcases rectangleDualCornerClamp_openAdj a w h A hadj with heq | hstep
      · simpa [heq] using ih tail.reachable
      · exact (actualConnected_of_adj _ _ hstep).trans (ih tail.reachable)

end
end PottsContinuity.PlanarMixed.Square
