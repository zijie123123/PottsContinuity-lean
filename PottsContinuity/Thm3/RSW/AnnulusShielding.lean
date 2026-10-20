module

public import PottsContinuity.Thm3.RSW.ShieldedAnnulus
public import PottsContinuity.Thm3.RSW.ErasureGraph
public import PottsContinuity.Thm3.RSW.FinitePath

/-! # Full-inner-box shielding supplies the actual annulus witness -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Vertices of the ambient carrier lying in the translated closed lattice
box. The definition applies to every radius and every ambient finite set. -/
def vertexBoxRegion (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (r : ℕ) :
    Set (V : Set (ℤ × ℤ)) :=
  {v | max |v.val.1-z.1| |v.val.2-z.2| ≤ (r : ℤ)}

/-- An actual annulus circuit survives closing all bonds outside its outer
box. Its simple polygon and bounded Jordan enclosure are unchanged. -/
theorem annulus_mem_inner_erasure (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (n : ℕ)
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hA : A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n)) :
    inducedConfigurationErasure (vertexBoxRegion V z (2*n)) A ∈
      finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) := by
  obtain ⟨m,P,hz,hann,hopen⟩ := hA
  refine ⟨m,P,hz,hann,?_⟩
  intro i
  obtain ⟨hi,hj,hadj⟩ := hopen i
  refine ⟨hi,hj,?_⟩
  rw [rcOpenGraph_boolConfigurationEquiv_symm] at hadj ⊢
  apply (openGraph_inducedConfigurationErasure_adj _ A _ _).mpr
  refine ⟨hadj, ?_, ?_⟩
  · change max |(P.vertex i).1-z.1| |(P.vertex i).2-z.2| ≤ ((2*n : ℕ) : ℤ)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hann i).2
  · change max |(P.vertex (i+1)).1-z.1| |(P.vertex (i+1)).2-z.2| ≤ ((2*n : ℕ) : ℤ)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hann (i+1)).2

/-- A dual screen must shield all primal clusters meeting the whole inner
box, not merely the center. That honest deterministic condition supplies a
cluster-confined annulus witness whenever the actual annulus event occurs. -/
theorem shieldedAnnulus_of_full_inner_shield (V : Finset (ℤ × ℤ))
    (W : Set (V : Set (ℤ × ℤ))) (z : ℤ × ℤ) (n : ℕ)
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (hA : A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n))
    (hshield : ∀ v ∈ vertexBoxRegion V z (2*n), ∀ w,
      ActualConnected (squareLattice.induce (V : Set (ℤ × ℤ))) A v w → w ∈ W) :
    A ∈ shieldedAnnulusEvent V W z n :=
  confinedWitness_of_inner_shield _ W _ A (annulus_mem_inner_erasure V z n A hA) hshield

end
end PottsContinuity.RSW
