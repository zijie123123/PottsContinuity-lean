module

public import PottsContinuity.Thm3.RSW.PolygonTranslation
public import PottsContinuity.Thm3.RSW.FiniteIso

/-! # Genuine sampled annulus circuits translate with their open graphs -/

@[expose] public section

namespace PottsContinuity.RSW
noncomputable section

/-- Transport the actual polygon, its annular location, open bonds and Jordan
enclosure along a coordinate translation of the sampled open graphs. -/
theorem annulusCircuit_translate_of_openIso
    (U V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (U : Set (ℤ × ℤ))).edgeSet → Bool)
    (η : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (c : ℤ × ℤ) (e : rcOpenGraph U ω ≃g rcOpenGraph V η)
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
    have hnew := e.map_rel_iff.mpr hadj
    have hu' : e u = ⟨(translatedLatticePolygon P c).vertex i,hiV⟩ := Subtype.ext hu
    have hv' : e v = ⟨(translatedLatticePolygon P c).vertex (i+1),hjV⟩ := Subtype.ext hv
    exact hu' ▸ hv' ▸ hnew

/-- Exact event equivalence, including translation of the center in both
directions and the genuine bounded Jordan region. -/
theorem annulusCircuit_translate_iff_openIso
    (U V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (U : Set (ℤ × ℤ))).edgeSet → Bool)
    (η : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)
    (c : ℤ × ℤ) (e : rcOpenGraph U ω ≃g rcOpenGraph V η)
    (hpos : ∀ u, (e u).val = FKC.latticeTranslate c u.val)
    (z : ℤ × ℤ) (n : ℕ) :
    η ∈ annulusCircuitEvent V (FKC.latticeTranslate c z) n ↔
      ω ∈ annulusCircuitEvent U z n := by
  constructor
  · intro hη
    have hneg : ∀ v, (e.symm v).val = FKC.latticeTranslate (-c) v.val := by
      intro v
      have hp := hpos (e.symm v)
      rw [e.apply_symm_apply] at hp
      have hh := congrArg (FKC.latticeTranslate (-c)) hp
      rw [FKC.latticeTranslate_neg_cancel] at hh
      exact hh.symm
    have h := annulusCircuit_translate_of_openIso V U η ω (-c) e.symm hneg
      (FKC.latticeTranslate c z) n hη
    simpa only [FKC.latticeTranslate_neg_cancel] using h
  · exact annulusCircuit_translate_of_openIso U V ω η c e hpos z n

end
end PottsContinuity.RSW
