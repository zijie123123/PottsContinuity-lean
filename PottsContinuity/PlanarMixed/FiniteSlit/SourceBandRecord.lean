module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceClosedPathGraph
public import PottsContinuity.PlanarMixed.OrderedCutActive
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PlanarMixed.CutExteriorReveals
public import PottsContinuity.PlanarMixed.FixedOpenWalk
public import PottsContinuity.PlanarMixed.SquareCrosscutData
public import PottsContinuity.PlanarMixed.RecordedArcBonds

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK Exploration BD12
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance sourceBandRecordEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

private theorem sourceInternalBonds_mono {V : Type*} [Finite V] (G : SimpleGraph V)
    (S T : Set V) (hST : S ⊆ T) : internalBonds G S ⊆ internalBonds G T := by
  classical
  intro e he
  simp only [internalBonds,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
  exact fun z hz => hST (he z hz)

/-- Every original support-internal bond is actually revealed, including
all marked path bonds and all chords internal to either support. -/
theorem sourcePathArcBonds_subset_exterior (w h : ℕ) (x : ℤ)
    (P : SourceWalkPair (rectangleGraph (0,0) w h)) :
    sourcePathArcBonds w h P ⊆ sourceExteriorReveal w h x P.secondEnd.val.2
      (Subtype.val '' {z | z ∈ P.first.support})
      (Subtype.val '' {z | z ∈ P.second.support}) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    left
    apply sourceInternalBonds_mono _ _ _ ?_ he
    intro z hz
    change Sum.inl z ∈ closedCutExterior _ _ _
    exact Or.inr ⟨z,⟨z,hz,rfl⟩,rfl⟩
  · apply Finset.mem_union.mpr
    right
    apply Finset.mem_union.mpr
    right
    apply sourceInternalBonds_mono _ _ _ ?_ he
    intro z hz
    change Sum.inl z ∈ closedCutExterior _ _ _
    exact Or.inr ⟨z,⟨z,hz,rfl⟩,rfl⟩

/-- An actually open revealed source bond remains open in the complete
record, without asking for a frozen-state identity. -/
theorem source_recorded_open_bond (w h : ℕ) {U : Type*} [Finite U]
    (H : SimpleGraph U) (j : RectangleVertex (0,0) w h ↪ U)
    (hSH : (rectangleGraph (0,0) w h).map j ≤ H)
    (R : Configuration (rectangleGraph (0,0) w h))
    (reveal : RevealMap (G := H)) (C : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((edgeRestriction (rectangleGraph (0,0) w h) R).map j) H)
    (e : (rectangleGraph (0,0) w h).edgeSet) (heR : e ∈ R)
    (heC : e ∈ embeddedConfigurationRestriction _ H j hSH C) :
    e ∈ embeddedConfigurationRestriction _ H j hSH (revealRecordConfiguration reveal C).val := by
  apply (mem_embeddedConfigurationRestriction _ H j hSH _ e).mpr
  apply Finset.mem_inter.mpr
  refine ⟨(mem_embeddedConfigurationRestriction _ H j hSH _ e).mp heC,?_⟩
  rw [hcarrier]
  exact embedded_removed_bond_exposed _ H j hSH R e heR

end
end PottsContinuity.PlanarMixed.FiniteSlit
