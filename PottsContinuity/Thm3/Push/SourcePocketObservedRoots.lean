module

public import PottsContinuity.Thm3.Push.SourcePocketRecordBound

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration
noncomputable section
local instance sourcePocketObservedRootsEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- A connection between the active support arcs joins the original roots
in every sample agreeing with the actual observed source record. -/
theorem sourcePocket_observed_roots_of_active_connection
    (w h : ℕ) (x : ℤ) (P : SourceWalkPair (rectangleGraph (0,0) w h))
    {U : Type*} [Finite U] (H : SimpleGraph U)
    (j : RectangleVertex (0,0) w h ↪ U) (hSH : (rectangleGraph (0,0) w h).map j ≤ H)
    (reveal : RevealMap (G := H)) (C ω : Configuration H)
    (hcarrier : reveal C = subgraphRemovedEdges ((sourcePocketActiveGraph w h x P).map j) H)
    (Q : SourceWalkPair (openGraph (rectangleGraph (0,0) w h)
      (embeddedConfigurationRestriction _ H j hSH C)))
    (hp : ∀ z, z ∈ Q.first.support ↔ z ∈ P.first.support)
    (hq : ∀ z, z ∈ Q.second.support ↔ z ∈ P.second.support)
    (hstates : ω ∩ reveal C = C ∩ reveal C)
    (hconn : embeddedConfigurationRestriction (sourcePocketActiveGraph w h x P) H j
      ((SimpleGraph.map_monotone j (edgeRestriction_le _ _)).trans hSH) ω ∈
      arcsConnectionEvent (sourcePocketActiveGraph w h x P)
        {z | z ∈ P.first.support} {z | z ∈ P.second.support}) :
    ActualConnected H ω (j P.firstStart) (j P.secondStart) := by
  let R := pocketAugmentedSourceReveal w h x P.secondEnd.val.2
    (Subtype.val '' {z | z ∈ P.first.support}) (Subtype.val '' {z | z ∈ P.second.support})
  have hpR : ∀ e : (rectangleGraph (0,0) w h).edgeSet, e.val ∈ Q.first.edges → e ∈ R :=
    fun e he => sourceExteriorReveal_subset_pocketAugmented _ _ _ _ _ _
      (sourceSupportWalk_bond_exposed w h x P Q.first (Or.inl (fun z hz => (hp z).mp hz)) e he)
  have hqR : ∀ e : (rectangleGraph (0,0) w h).edgeSet, e.val ∈ Q.second.edges → e ∈ R :=
    fun e he => sourceExteriorReveal_subset_pocketAugmented _ _ _ _ _ _
      (sourceSupportWalk_bond_exposed w h x P Q.second (Or.inr (fun z hz => (hq z).mp hz)) e he)
  let p := recordedSourceOpenWalk w h H j hSH R reveal C hcarrier Q.first hpR
  let q := recordedSourceOpenWalk w h H j hSH R reveal C hcarrier Q.second hqR
  have hpS : p.support = Q.first.support := recordedSourceOpenWalk_support w h H j hSH R reveal C hcarrier Q.first hpR
  have hqS : q.support = Q.second.support := recordedSourceOpenWalk_support w h H j hSH R reveal C hcarrier Q.second hqR
  have hsub : (revealRecordConfiguration reveal C).val ⊆ ω := by
    intro e he
    change e ∈ C ∩ reveal C at he
    rw [← hstates] at he
    exact (Finset.mem_inter.mp he).1
  let f := embeddedOpenRestrictionHom _ H j hSH (revealRecordConfiguration reveal C).val
  let g : openGraph H (revealRecordConfiguration reveal C).val →g openGraph H ω :=
    SimpleGraph.Hom.ofLE (openGraph_mono hsub)
  obtain ⟨a,ha,b,hb,hab⟩ := hconn
  have hleft := openWalk_support_actualConnected _ _ p
    (hpS.symm ▸ (hp P.firstStart).mpr P.first.start_mem_support) (hpS.symm ▸ (hp a).mpr ha)
  have hright := openWalk_support_actualConnected _ _ q
    (hqS.symm ▸ (hq b).mpr hb) (hqS.symm ▸ (hq P.secondStart).mpr P.second.start_mem_support)
  have hleftH := hleft.map (g.comp f)
  have hrightH := hright.map (g.comp f)
  have hmiddle := hab.map (embeddedOpenRestrictionHom (sourcePocketActiveGraph w h x P) H j
    ((SimpleGraph.map_monotone j (edgeRestriction_le _ _)).trans hSH) ω)
  exact (hleftH.trans hmiddle).trans hrightH

end
end PottsContinuity.Push
