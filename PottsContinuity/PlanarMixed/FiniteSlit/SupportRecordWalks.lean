module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceBandRecord
public import PottsContinuity.PlanarMixed.FiniteSlit.SourceClosedPathGraph
public import PottsContinuity.PlanarMixed.OrderedCutActive
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PlanarMixed.CutExteriorReveals
public import PottsContinuity.PlanarMixed.FixedOpenWalk
public import PottsContinuity.PlanarMixed.SquareCrosscutData

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 Exploration
noncomputable section
local instance supportRecordWalksEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- An actual open source walk remains open in the recorded sample when
all its bonds were revealed. Its vertices and endpoints are unchanged. -/
def recordedSourceOpenWalk (w h : ℕ) {U : Type*} [Finite U]
    (H : SimpleGraph U) (j : RectangleVertex (0,0) w h ↪ U)
    (hSH : (rectangleGraph (0,0) w h).map j ≤ H)
    (R : Configuration (rectangleGraph (0,0) w h))
    (reveal : RevealMap (G := H)) (C : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((edgeRestriction (rectangleGraph (0,0) w h) R).map j) H)
    {a b : RectangleVertex (0,0) w h}
    (p : (openGraph (rectangleGraph (0,0) w h)
      (embeddedConfigurationRestriction _ H j hSH C)).Walk a b)
    (hR : ∀ e : (rectangleGraph (0,0) w h).edgeSet, e.val ∈ p.edges → e ∈ R) :
    (openGraph (rectangleGraph (0,0) w h)
      (embeddedConfigurationRestriction _ H j hSH (revealRecordConfiguration reveal C).val)).Walk a b :=
  fixedOpenWalk _ _ (p.mapLe (openGraph_le _ _)) (by
    intro e he
    have hp : e ∈ p.edges := by simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    have hopen : e ∈ openEdges (rectangleGraph (0,0) w h)
        (embeddedConfigurationRestriction _ H j hSH C) := by
      simpa only [openGraph_edgeSet] using p.edges_subset_edgeSet hp
    obtain ⟨eS,heS,hee⟩ := hopen
    exact ⟨eS,source_recorded_open_bond w h H j hSH R reveal C hcarrier eS
      (hR eS (hee ▸ hp)) heS,hee⟩)

/-- Recording changes no vertex of the actual walk. -/
theorem recordedSourceOpenWalk_support (w h : ℕ) {U : Type*} [Finite U]
    (H : SimpleGraph U) (j : RectangleVertex (0,0) w h ↪ U)
    (hSH : (rectangleGraph (0,0) w h).map j ≤ H)
    (R : Configuration (rectangleGraph (0,0) w h))
    (reveal : RevealMap (G := H)) (C : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((edgeRestriction (rectangleGraph (0,0) w h) R).map j) H)
    {a b : RectangleVertex (0,0) w h}
    (p : (openGraph (rectangleGraph (0,0) w h)
      (embeddedConfigurationRestriction _ H j hSH C)).Walk a b)
    (hR : ∀ e : (rectangleGraph (0,0) w h).edgeSet, e.val ∈ p.edges → e ∈ R) :
    (recordedSourceOpenWalk w h H j hSH R reveal C hcarrier p hR).support = p.support := by
  simp only [recordedSourceOpenWalk,fixedOpenWalk_support,SimpleGraph.Walk.support_mapLe_eq_support]

/-- Every actual source-walk bond whose endpoints lie in either fixed marked
support is exposed, even if it is not a bond of the fixed geometric walk. -/
theorem sourceSupportWalk_bond_exposed (w h : ℕ) (x : ℤ)
    (P : SourceWalkPair (rectangleGraph (0,0) w h))
    {C : Configuration (rectangleGraph (0,0) w h)} {a b : RectangleVertex (0,0) w h}
    (p : (openGraph (rectangleGraph (0,0) w h) C).Walk a b)
    (hsub : (∀ z ∈ p.support, z ∈ P.first.support) ∨
      (∀ z ∈ p.support, z ∈ P.second.support))
    (e : (rectangleGraph (0,0) w h).edgeSet) (he : e.val ∈ p.edges) :
    e ∈ sourceExteriorReveal w h x P.secondEnd.val.2
      (Subtype.val '' {z | z ∈ P.first.support})
      (Subtype.val '' {z | z ∈ P.second.support}) := by
  classical
  apply sourcePathArcBonds_subset_exterior w h x P
  rcases hsub with hp | hq
  · apply Finset.mem_union.mpr
    left
    simp only [internalBonds,Finset.mem_filter,Finset.mem_univ,true_and]
    exact fun z hz => hp z (SimpleGraph.Walk.mem_support_of_mem_edges he hz)
  · apply Finset.mem_union.mpr
    right
    simp only [internalBonds,Finset.mem_filter,Finset.mem_univ,true_and]
    exact fun z hz => hq z (SimpleGraph.Walk.mem_support_of_mem_edges he hz)

end
end PottsContinuity.PlanarMixed.FiniteSlit
