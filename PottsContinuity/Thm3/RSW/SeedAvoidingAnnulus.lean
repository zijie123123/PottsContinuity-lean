module

public import PottsContinuity.Thm3.RSW.SeedAvoidingWitness
public import PottsContinuity.Thm3.RSW.AnnulusShielding
public import PottsContinuity.Thm3.RSW.PolygonHorizontalExtent
public import PottsContinuity.Thm3.RSW.PolygonPaths

/-! # A genuine annulus witness avoids clusters confined to its left -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- A polygon surrounding z has a vertex outside any region lying to the
left of z. If seed clusters stay in that region, its entire actual open cycle
avoids them. Only the selected polygon bonds are retained as the witness. -/
theorem seedAvoidingAnnulus_of_coreShield_and_rightExit
    (V : Finset (ℤ × ℤ)) (S : Finset (V : Set (ℤ × ℤ)))
    (W₁ W₂ : Set (V : Set (ℤ × ℤ))) (z : ℤ × ℤ) (n : ℕ)
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hAnn : A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n))
    (hseed : ∀ s ∈ S, ∀ v,
      ActualConnected (squareLattice.induce (V : Set (ℤ × ℤ))) A s v → v ∈ W₁)
    (hleft : ∀ v ∈ W₁, v.val.1 ≤ z.1)
    (hshield : ∀ v ∈ vertexBoxRegion V z (2*n), ∀ w,
      ActualConnected (squareLattice.induce (V : Set (ℤ × ℤ))) A v w → w ∈ W₂) :
    A ∈ seedAvoidingConfinedWitnessEvent _ S W₂
      (finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n)) := by
  classical
  obtain ⟨m,P,hz,hann,hopen⟩ := hAnn
  have hmem : ∀ i, P.vertex i ∈ V := by
    intro i
    obtain ⟨hi,hj,hadj⟩ := hopen i
    exact hi
  let u : ZMod (m+3) → (V : Set (ℤ × ℤ)) := fun i => ⟨P.vertex i,hmem i⟩
  have hcycle : ∀ i, (openGraph _ A).Adj (u i) (u (i+1)) := by
    intro i
    obtain ⟨hi,hj,hadj⟩ := hopen i
    rw [rcOpenGraph_boolConfigurationEquiv_symm] at hadj
    exact hadj
  obtain ⟨j,hj⟩ := latticePolygon_exists_vertex_right_of_center P z hz
  let D : Set (V : Set (ℤ × ℤ)) := {v | ∃ i, P.vertex i = v.val}
  let B := inducedConfigurationErasure D A
  have hBAnn : B ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) := by
    refine ⟨m,P,hz,hann,?_⟩
    intro i
    refine ⟨hmem i,hmem (i+1),?_⟩
    rw [rcOpenGraph_boolConfigurationEquiv_symm]
    exact (openGraph_inducedConfigurationErasure_adj D A _ _).mpr
      ⟨hcycle i,⟨i,rfl⟩,⟨i+1,rfl⟩⟩
  refine ⟨B,inducedConfigurationErasure_subset D A,hBAnn,?_⟩
  intro e he v hv
  obtain ⟨i,hi⟩ := ((mem_inducedConfigurationErasure D A e).mp he).2 v hv
  have hiv : u i = v := Subtype.ext hi
  have hvj : ActualConnected _ A v (u j) := by
    rw [← hiv]
    exact cyclic_index_reachable (openGraph _ A) m u hcycle i j
  constructor
  · rintro ⟨s,hs,hsv⟩
    have hW := hseed s hs (u j) (hsv.trans hvj)
    have hle := hleft (u j) hW
    change (P.vertex j).1 ≤ z.1 at hle
    exact (not_lt_of_ge hle) hj
  · apply hshield v
    change max |v.val.1-z.1| |v.val.2-z.2| ≤ ((2*n:ℕ):ℤ)
    rw [← hi]
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hann i).2

end
end PottsContinuity.RSW
