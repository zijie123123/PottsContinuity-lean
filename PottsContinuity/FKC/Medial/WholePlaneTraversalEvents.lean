-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/WholePlaneTraversalEvents.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.WholePlanePairing
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Clopen

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

/-- A deterministic one-step choice for a prescribed local edge state. -/
def medialStateStep (b : Bool) (p : LatticePort) : LatticePort :=
  LatticePort.cornerPair (LatticePort.localPair (fun _ : LatticeBond => b) p)

@[simp] theorem wholePlaneMedialStep_eq_medialStateStep (ω : LatticeConfiguration)
    (p : LatticePort) :
    wholePlaneMedialStep ω p =
      medialStateStep (latticeConfigurationBondState ω p.bond) p := by
  simp [wholePlaneMedialStep_apply, medialStateStep, LatticePort.localPair]

/-- The actual port after `n` alternating pairing steps. -/
def medialIteratePort (ω : LatticeConfiguration) (p : LatticePort) (n : ℕ) : LatticePort :=
  (wholePlaneMedialStep ω ^ n) p

@[simp] theorem medialIteratePort_succ (ω : LatticeConfiguration) (p : LatticePort)
    (n : ℕ) :
    medialIteratePort ω p (n + 1) = wholePlaneMedialStep ω (medialIteratePort ω p n) := by
  simp [medialIteratePort, pow_succ', Equiv.Perm.mul_apply]

end
end PottsContinuity.FKC.Medial
