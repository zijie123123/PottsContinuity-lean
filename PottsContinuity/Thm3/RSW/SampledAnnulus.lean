module

public import PottsContinuity.Thm3.RSW.AnnulusTranslation
public import PottsContinuity.Thm3.RSW.TranslatedAnnulus

/-! # Actual annulus polygons in the common sampled ambient graph -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Translate an actual polygon along the original-edge open graph homomorphism. -/
theorem annulusCircuit_translate_of_openHom
    (U V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (U : Set (ℤ × ℤ))).edgeSet → Bool)
    (η : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (c : ℤ × ℤ) (e : rcOpenGraph U ω →g rcOpenGraph V η)
    (hpos : ∀ u, (e u).val = FKC.latticeTranslate c u.val)
    (z : ℤ × ℤ) (n : ℕ) (hω : ω ∈ annulusCircuitEvent U z n) :
    η ∈ annulusCircuitEvent V (FKC.latticeTranslate c z) n := by
  obtain ⟨m,P,hz,hann,hopen⟩ := hω
  refine ⟨m,translatedLatticePolygon P c,
    translatedLatticePolygon_center P c z _ hz,?_,?_⟩
  · intro i
    simpa [translatedLatticePolygon,FKC.latticeTranslate] using hann i
  · intro i
    obtain ⟨hi,hj,hadj⟩ := hopen i
    let u : (U : Set (ℤ × ℤ)) := ⟨P.vertex i,hi⟩
    let v : (U : Set (ℤ × ℤ)) := ⟨P.vertex (i+1),hj⟩
    have hu : (e u).val = (translatedLatticePolygon P c).vertex i := hpos u
    have hv : (e v).val = (translatedLatticePolygon P c).vertex (i+1) := hpos v
    have hiV : (translatedLatticePolygon P c).vertex i ∈ V := hu ▸ (e u).property
    have hjV : (translatedLatticePolygon P c).vertex (i+1) ∈ V := hv ▸ (e v).property
    refine ⟨hiV,hjV,?_⟩
    have hnew := e.map_rel hadj
    have hu' : e u = ⟨(translatedLatticePolygon P c).vertex i,hiV⟩ := Subtype.ext hu
    have hv' : e v = ⟨(translatedLatticePolygon P c).vertex (i+1),hjV⟩ := Subtype.ext hv
    exact hu' ▸ hv' ▸ hnew


/-- Literal edge restriction maps its open graph into the common sampled graph. -/
def finiteBoolRestrictionOpenHom (U V : Finset (ℤ × ℤ))
    (f : (U : Set (ℤ × ℤ)) ↪ (V : Set (ℤ × ℤ)))
    (hUV : (squareLattice.induce (U : Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (V : Set (ℤ × ℤ)))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    rcOpenGraph U (finiteBoolRestriction U V f hUV ω) →g rcOpenGraph V ω where
  toFun := f
  map_rel' := by
    intro u v huv
    let A := boolConfigurationEquiv _ ω
    have hinner := finiteBoolRestriction_equiv U V f hUV A
    change finiteBoolRestriction U V f hUV ((boolConfigurationEquiv _).symm
      (boolConfigurationEquiv _ ω)) = _ at hinner
    simp only [Equiv.symm_apply_apply] at hinner
    rw [hinner,rcOpenGraph_boolConfigurationEquiv_symm] at huv
    have houter := rcOpenGraph_boolConfigurationEquiv_symm V A
    simp only [A,Equiv.symm_apply_apply] at houter
    rw [houter]
    exact (embeddedRestrictionOpenHom _ _ f hUV A).map_rel huv

/-- A local sampled annulus is a genuine translated annulus in the ambient
sample, retaining its actual polygon edges and bounded Jordan enclosure. -/
theorem translatedAnnulusEvent_subset_actualAnnulus
    (V : Finset (ℤ × ℤ)) (m : ℕ) (c : ℤ × ℤ)
    (hwindow : ∀ z ∈ box (8*m), (z.1+c.1,z.2+c.2) ∈ V) :
    translatedAnnulusEvent V m c hwindow ⊆ annulusCircuitEvent V c m := by
  intro ω hω
  have h := annulusCircuit_translate_of_openHom (box (8*m)) V _ ω c
    (finiteBoolRestrictionOpenHom (box (8*m)) V
      (translatedWindowVertexEmbedding (box (8*m)) V c hwindow)
      (translatedWindow_graph_le (box (8*m)) V c hwindow) ω)
    (fun _ => rfl) (0,0) m hω
  have hc : FKC.latticeTranslate c (0,0) = c := by ext <;> simp [FKC.latticeTranslate]
  simpa only [hc] using h

end
end PottsContinuity.RSW
