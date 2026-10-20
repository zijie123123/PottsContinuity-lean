module

public import PottsContinuity.DualityExt.PositiveEmbeddedDualEdgeState
public import PottsContinuity.DualityExt.PositiveSubgraphDualEdgeEquiv
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

noncomputable section

variable {a : LatticeVertex} {w h : ℕ}

/-- An open dual adjacency forces its crossed source edge to be closed in
the configuration from which the finite dual state was formed. -/
theorem embeddedRectangleDualOpenAdj_crossedSourceClosed
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (f : V ↪ RectangleVertex a w h)
    (hG : G.map f ≤ rectangleGraph a w h)
    (C : Configuration G) (g : G.edgeSet)
    (u v : RectangleDualVertex a w h)
    (hcross : Sym2.map (fun z : RectangleDualVertex a w h => z.1) (s(u, v)) =
      (dualBondOfPrimal (rectanglePrimalEdgeBond a w h
        (subgraphEdgeEmbedding hG (isolatedExtensionEdgeEquiv G f g)))).toSym2)
    (hopen : (openGraph (rectangleSubgraphDualGraph hG)
        (rectangleSubgraphDualConfigurationEquiv hG
          (isolatedExtensionConfigurationEquiv G f C))).Adj u v) :
    g ∉ C := by
  let C' := isolatedExtensionConfigurationEquiv G f C
  let g' := isolatedExtensionEdgeEquiv G f g
  have hopen' := (openGraph_adj (rectangleSubgraphDualGraph hG)
    (rectangleSubgraphDualConfigurationEquiv hG
      C') u v).mp hopen
  rcases hopen' with ⟨d, hd, hduv⟩
  let e := rectangleSubgraphDualEdgeEmbedding hG g'
  have helabel := rectangleSubgraphDualEdgeEquiv_crossingBond hG
    g'
  have hdlabel : Sym2.map (fun z : RectangleDualVertex a w h => z.1) d.val =
      Sym2.map (fun z : RectangleDualVertex a w h => z.1) e.val := by
    calc
      Sym2.map (fun z : RectangleDualVertex a w h => z.1) d.val =
          Sym2.map (fun z : RectangleDualVertex a w h => z.1) (s(u, v)) := by
            rw [hduv]
      _ = (dualBondOfPrimal (rectanglePrimalEdgeBond a w h
            (subgraphEdgeEmbedding hG g'))).toSym2 := hcross
      _ = Sym2.map (fun z : RectangleDualVertex a w h => z.1) e.val := helabel.symm
  have hde : d = e := by
    apply Subtype.ext
    exact Sym2.map.injective (Subtype.val_injective) hdlabel
  have heopen : e ∈ rectangleSubgraphDualConfigurationEquiv hG C' := by
    rw [← hde]
    exact hd
  change rectangleSubgraphDualEdgeEmbedding hG g' ∈
    rectangleSubgraphDualConfigurationEquiv hG C' at heopen
  have hgclosed : g' ∉ C' :=
    (rectangleSubgraphDualConfigurationEquiv_edgeState hG C' g').mp heopen
  intro hg
  apply hgclosed
  have hmem : g' ∈ C' ↔ g ∈ C := by
    simp only [g', C', isolatedExtensionConfigurationEquiv_val, Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  exact hmem.mpr hg

end

end PottsContinuity.DualityExt
