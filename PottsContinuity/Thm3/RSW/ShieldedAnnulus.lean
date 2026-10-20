module

public import PottsContinuity.Thm3.RSW.ConfinedWitness
public import PottsContinuity.Thm3.RSW.StoppingJointUpper
public import PottsContinuity.Thm3.RSW.AnnulusCircuit

/-!
# Shielded annulus events for Lemma 4

The shielding condition concerns the whole ambient sampled cluster of every
witness edge, not merely the location of the circuit path. The circuit remains
the genuine simple lattice polygon with Jordan enclosure from AnnulusCircuit.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- A source annulus circuit witnessed by open bonds all of whose incident
ambient clusters remain inside the prescribed vertex region. -/
def shieldedAnnulusEvent (V : Finset (ℤ × ℤ)) (W : Set (V : Set (ℤ × ℤ)))
    (z : ℤ × ℤ) (n : ℕ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  confinedWitnessEvent _ W (finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n))

/-- The exact free induced-region probability of the actual annulus event,
read after extension by closed bonds to the ambient carrier. -/
def inducedAnnulusProbability (V : Finset (ℤ × ℤ))
    (W : Set (V : Set (ℤ × ℤ))) (θ : Parameters) (z : ℤ × ℤ) (n : ℕ) : ℝ :=
  (measure ((squareLattice.induce (V : Set (ℤ × ℤ))).induce W)
    θ (BoundaryCondition.free ∅)
    {B | inducedConfigurationExtension W B ∈
      finiteBoolEvent V (fun ω => ω ∈ annulusCircuitEvent V z n)}).toReal

end
end PottsContinuity.RSW
