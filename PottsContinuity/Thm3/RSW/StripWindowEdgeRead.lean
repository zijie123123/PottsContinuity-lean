module

public import PottsContinuity.Thm3.RSW.StripAsymmetricReadMeasures

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Closed extension preserves every actual source-window bond. -/
theorem stripWindowPlaneConfiguration_edge (n M : ℕ)
    (C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))))
    (f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet) :
    stripWindowPlaneConfiguration n M C ((stripWindowPlaneEmbedding n M).mapEdgeSet f) =
      (boolConfigurationEquiv _).symm C f := by
  classical
  simp only [stripWindowPlaneConfiguration,boolConfigurationEquiv,
    Equiv.coe_fn_symm_mk,decide_eq_decide]
  change ((stripWindowPlaneEmbedding n M).mapEdgeSet f ∈
    C.map (stripWindowPlaneEmbedding n M).mapEdgeSet) ↔ f ∈ C
  constructor
  · intro h
    obtain ⟨g,hg,hgf⟩ := Finset.mem_map.mp h
    exact (stripWindowPlaneEmbedding n M).mapEdgeSet.injective hgf ▸ hg
  · intro h
    exact Finset.mem_map.mpr ⟨f,h,rfl⟩

/-- Literal finite reads agree whenever the original physical edge labels
agree, independently of any measure or boundary partition. -/
theorem stripWindowOriginalRead_edge (n M : ℕ)
    (C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))))
    (f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet)
    (e : (stripGraph n).edgeSet)
    (he : Sym2.map Subtype.val f.val=Sym2.map Subtype.val e.val) :
    stripWindowOriginalRead n M C e=(boolConfigurationEquiv _).symm C f := by
  have hmap : (stripWindowPlaneEmbedding n M).mapEdgeSet f =
      (stripPlaneEmbedding n).mapEdgeSet e := Subtype.ext he
  change stripWindowPlaneConfiguration n M C ((stripPlaneEmbedding n).mapEdgeSet e)=_
  rw [← hmap,stripWindowPlaneConfiguration_edge]

end
end PottsContinuity.RSW
