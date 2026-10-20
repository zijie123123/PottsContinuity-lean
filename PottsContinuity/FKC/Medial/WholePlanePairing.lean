-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/WholePlanePairing.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.LatticePorts
public import PottsContinuity.FKC.FiniteFK.BoxCylinders
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Clopen

@[expose] public section

open Set

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The square-lattice edge underlying a normalized actual lattice bond. -/
def latticeBondEdge (b : LatticeBond) : squareLattice.edgeSet :=
  ⟨b.toSym2, b.toSym2_mem_edgeSet⟩

/-- Read the actual original-edge state at a bond, without introducing a second
configuration carrier. -/
def latticeConfigurationBondState (ω : LatticeConfiguration) (b : LatticeBond) : Bool :=
  ω (latticeBondEdge b)

@[simp] theorem latticeConfigurationBondState_eq (ω : LatticeConfiguration) (b : LatticeBond) :
    latticeConfigurationBondState ω b = ω ⟨b.toSym2, b.toSym2_mem_edgeSet⟩ := rfl

/-- The configuration-dependent actual local pairing as a permutation of all
full-plane medial ports. -/
def configurationLocalPairing (ω : LatticeConfiguration) : Equiv.Perm LatticePort where
  toFun := LatticePort.localPair (latticeConfigurationBondState ω)
  invFun := LatticePort.localPair (latticeConfigurationBondState ω)
  left_inv := LatticePort.localPair_involutive _
  right_inv := LatticePort.localPair_involutive _

/-- The actual corner crossing pairing, as a permutation of the entire port set. -/
def wholePlaneCornerPairing : Equiv.Perm LatticePort where
  toFun := LatticePort.cornerPair
  invFun := LatticePort.cornerPair
  left_inv := LatticePort.cornerPair_involutive
  right_inv := LatticePort.cornerPair_involutive

/-- One alternating medial step: first use the actual FK local pairing, then
cross the actual square-corner medial edge. -/
def wholePlaneMedialStep (ω : LatticeConfiguration) : Equiv.Perm LatticePort :=
  (configurationLocalPairing ω).trans wholePlaneCornerPairing

@[simp] theorem wholePlaneMedialStep_apply (ω : LatticeConfiguration) (p : LatticePort) :
    wholePlaneMedialStep ω p =
      LatticePort.cornerPair (LatticePort.localPair (latticeConfigurationBondState ω) p) := rfl

@[simp] theorem configurationLocalPairing_faceBase_of_open (ω : LatticeConfiguration)
    (p : LatticePort) (h : latticeConfigurationBondState ω p.bond = true) :
    (configurationLocalPairing ω p).faceBase = p.faceBase := by
  change (LatticePort.localPair (latticeConfigurationBondState ω) p).faceBase = p.faceBase
  change ω ⟨p.bond.toSym2, p.bond.toSym2_mem_edgeSet⟩ = true at h
  simp [LatticePort.localPair, latticeConfigurationBondState, latticeBondEdge, h]

@[simp] theorem configurationLocalPairing_primalVertex_of_closed (ω : LatticeConfiguration)
    (p : LatticePort) (h : latticeConfigurationBondState ω p.bond = false) :
    (configurationLocalPairing ω p).primalVertex = p.primalVertex := by
  change (LatticePort.localPair (latticeConfigurationBondState ω) p).primalVertex = p.primalVertex
  change ω ⟨p.bond.toSym2, p.bond.toSym2_mem_edgeSet⟩ = false at h
  simp [LatticePort.localPair, latticeConfigurationBondState, latticeBondEdge, h]

@[simp] theorem wholePlaneCornerPairing_faceBase (p : LatticePort) :
    (wholePlaneCornerPairing p).faceBase = p.faceBase := LatticePort.cornerPair_faceBase p

@[simp] theorem wholePlaneCornerPairing_primalVertex (p : LatticePort) :
    (wholePlaneCornerPairing p).primalVertex = p.primalVertex :=
  LatticePort.cornerPair_primalVertex p

end
end PottsContinuity.FKC.Medial
