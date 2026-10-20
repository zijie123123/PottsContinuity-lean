module

public import PottsContinuity.Thm3.RSW.TiltedStripWindowReads
public import PottsContinuity.Thm3.RSW.TiltedFiniteEdgeStrict
public import PottsContinuity.Thm3.RSW.TiltedStripMarginalFiniteWindow

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- A literal original edge retained by the finite window is read without
any change of its sampled state. -/
theorem tiltedStripWindowOriginalRead_edge (N : ℕ) (t : ℝ) (M : ℕ)
    (e : (tiltedStripGraph N t).edgeSet)
    (f : (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))).edgeSet)
    (hpair : Sym2.map Subtype.val f.val = Sym2.map Subtype.val e.val)
    (C : Configuration (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))) :
    tiltedStripWindowOriginalRead N t M C e =
      (boolConfigurationEquiv _).symm C f := by
  classical
  have heq : (tiltedWindowPlaneEmbedding N M t).mapEdgeSet f =
      (tiltedPlaneEmbedding N t).mapEdgeSet e := Subtype.ext hpair
  have hmem : (tiltedPlaneEmbedding N t).mapEdgeSet e ∈
      C.map (tiltedWindowPlaneEmbedding N M t).mapEdgeSet ↔ f ∈ C := by
    rw [← heq]
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨g,hg,hgf⟩
      have h : g = f := (tiltedWindowPlaneEmbedding N M t).mapEdgeSet.injective hgf
      exact h ▸ hg
    · intro hf
      exact ⟨f,hf,rfl⟩
  change tiltedWindowPlaneConfiguration N M t C ((tiltedPlaneEmbedding N t).mapEdgeSet e) =
    (boolConfigurationEquiv _).symm C f
  rw [← heq]
  simp only [tiltedWindowPlaneConfiguration,boolConfigurationEquiv,
    Equiv.coe_fn_symm_mk,decide_eq_decide]
  change (tiltedWindowPlaneEmbedding N M t).mapEdgeSet f ∈
    C.map (tiltedWindowPlaneEmbedding N M t).mapEdgeSet ↔ f ∈ C
  rw [heq]
  exact hmem

end
end PottsContinuity.RSW
