module

public import PottsContinuity.Thm3.RSW.RootedWitnessRecord
public import PottsContinuity.Thm3.RSW.AnnulusShielding

/-! # A core-seed record determines the actual shielded annulus event -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Exploration
noncomputable section
local instance annulusSeedRecordRegionFintype (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (r : ℕ) :
    Fintype (vertexBoxRegion V z r) := Fintype.ofFinite _

/-- The genuine annulus event reads only the original bonds in its outer
2n box, in either direction of the literal edge-erasure equality. -/
theorem annulusEvent_inner_erasure_iff
    (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (n : ℕ)
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :
    A ∈ finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) ↔
      inducedConfigurationErasure (vertexBoxRegion V z (2*n)) A ∈
        finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n) := by
  refine ⟨annulus_mem_inner_erasure V z n A,?_⟩
  exact fun h => finiteBoolEvent_isUpperSet V _ (annulusCircuitEvent_isUpperSet V z n)
    (inducedConfigurationErasure_subset _ A) h

end
end PottsContinuity.RSW
