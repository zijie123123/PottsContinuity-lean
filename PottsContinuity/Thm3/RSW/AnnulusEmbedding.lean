module

public import PottsContinuity.Thm3.RSW.AnnulusShielding

/-! # Annulus witnesses under position-preserving open graph embeddings -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Closing all exterior bonds does not create annulus witnesses outside the
embedded carrier. The literal polygon and its Jordan interior are retained. -/
theorem annulus_event_iff_of_openGraph_map
    (U V : Finset (ℤ × ℤ))
    (f : (U : Set (ℤ × ℤ)) ↪ (V : Set (ℤ × ℤ)))
    (hpos : ∀ u, (f u).val = u.val)
    (A : Configuration (squareLattice.induce (U : Set (ℤ × ℤ))))
    (B : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hmap : openGraph (squareLattice.induce (V : Set (ℤ × ℤ))) B =
      (openGraph (squareLattice.induce (U : Set (ℤ × ℤ))) A).map f)
    (z : ℤ × ℤ) (n : ℕ) :
    B ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) ↔
      A ∈ finiteBoolEvent U (fun ω => ω ∈ annulusCircuitEvent U z n) := by
  constructor
  · rintro ⟨m,P,hz,hann,hopen⟩
    refine ⟨m,P,hz,hann,?_⟩
    intro i
    obtain ⟨hi,hj,hadj⟩ := hopen i
    rw [rcOpenGraph_boolConfigurationEquiv_symm, hmap] at hadj
    obtain ⟨u,v,huv,hu,hv⟩ := (SimpleGraph.map_adj f _ _ _).mp hadj
    have huval : u.val = P.vertex i := (hpos u).symm.trans (congrArg Subtype.val hu)
    have hvval : v.val = P.vertex (i+1) := (hpos v).symm.trans (congrArg Subtype.val hv)
    have hiU : P.vertex i ∈ U := huval ▸ u.property
    have hjU : P.vertex (i+1) ∈ U := hvval ▸ v.property
    refine ⟨hiU,hjU,?_⟩
    rw [rcOpenGraph_boolConfigurationEquiv_symm]
    have hu' : u = ⟨P.vertex i,hiU⟩ := Subtype.ext huval
    have hv' : v = ⟨P.vertex (i+1),hjU⟩ := Subtype.ext hvval
    exact hu' ▸ hv' ▸ huv
  · rintro ⟨m,P,hz,hann,hopen⟩
    refine ⟨m,P,hz,hann,?_⟩
    intro i
    obtain ⟨hi,hj,hadj⟩ := hopen i
    let u : (U : Set (ℤ × ℤ)) := ⟨P.vertex i,hi⟩
    let v : (U : Set (ℤ × ℤ)) := ⟨P.vertex (i+1),hj⟩
    have hup : (f u).val = P.vertex i := hpos u
    have hvp : (f v).val = P.vertex (i+1) := hpos v
    have hiV : P.vertex i ∈ V := hup ▸ (f u).property
    have hjV : P.vertex (i+1) ∈ V := hvp ▸ (f v).property
    refine ⟨hiV,hjV,?_⟩
    rw [rcOpenGraph_boolConfigurationEquiv_symm, hmap]
    apply (SimpleGraph.map_adj f _ _ _).mpr
    refine ⟨u,v,?_,Subtype.ext (hpos u),Subtype.ext (hpos v)⟩
    rw [rcOpenGraph_boolConfigurationEquiv_symm] at hadj
    exact hadj

end
end PottsContinuity.RSW
