module

public import PottsContinuity.PlanarTopology.KSTCorridorTranspose
public import PottsContinuity.PlanarTopology.DualConfigurationTranslation
public import PottsContinuity.PD.Duality.BoxDihedral
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Coordinate interchange of a normalized original lattice bond. -/
def transposeLatticeBond (b : LatticeBond) : LatticeBond :=
  ⟨b.base.swap,match b.axis with | .horizontal => .vertical | .vertical => .horizontal⟩

theorem latticeConfigurationBondState_transpose (ω : LatticeConfiguration) (b : LatticeBond) :
    latticeConfigurationBondState (latticeConfigurationIsoHomeomorph latticeTransposeIso ω) b =
      latticeConfigurationBondState ω (transposeLatticeBond b) := by
  change latticeConfigurationIsoHomeomorph latticeTransposeIso ω (latticeBondEdge b) = _
  rw [latticeConfigurationIsoHomeomorph_apply]
  apply congrArg ω
  apply Subtype.ext
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [transposeLatticeBond,latticeBondEdge,LatticeBond.toSym2,LatticeBond.source,
    LatticeBond.target,SimpleGraph.Iso.mapEdgeSet,SimpleGraph.Hom.mapEdgeSet,latticeTransposeIso,Prod.swap]

theorem wholePlaneDualConfiguration_transpose (ω : LatticeConfiguration) :
    wholePlaneDualConfigurationHomeomorph (latticeConfigurationIsoHomeomorph latticeTransposeIso ω) =
      latticeConfigurationIsoHomeomorph latticeTransposeIso (wholePlaneDualConfigurationHomeomorph ω) := by
  funext e
  obtain ⟨b,rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState
    (wholePlaneDualConfigurationHomeomorph (latticeConfigurationIsoHomeomorph latticeTransposeIso ω)) b =
    latticeConfigurationBondState
      (latticeConfigurationIsoHomeomorph latticeTransposeIso (wholePlaneDualConfigurationHomeomorph ω)) b
  rw [wholePlaneDualConfigurationHomeomorph_bondState,latticeConfigurationBondState_transpose,
    latticeConfigurationBondState_transpose,wholePlaneDualConfigurationHomeomorph_bondState]
  congr 2
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> rfl

theorem transposeConfiguration_twice (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso
      (latticeConfigurationIsoHomeomorph latticeTransposeIso ω) = ω := by
  funext e
  obtain ⟨b,rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState
    (latticeConfigurationIsoHomeomorph latticeTransposeIso
      (latticeConfigurationIsoHomeomorph latticeTransposeIso ω)) b = latticeConfigurationBondState ω b
  rw [latticeConfigurationBondState_transpose,latticeConfigurationBondState_transpose]
  congr 1
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> rfl

theorem transposeConfiguration_translate (a : LatticeVertex) (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso (edgeTranslate a ω) =
      edgeTranslate a.swap (latticeConfigurationIsoHomeomorph latticeTransposeIso ω) := by
  funext e
  simp only [latticeConfigurationTranslate_apply,latticeConfigurationIsoHomeomorph_apply]
  congr 1
  apply Subtype.ext
  simp only [SimpleGraph.Iso.mapEdgeSet_apply,SimpleGraph.Hom.mapEdgeSet_coe,Sym2.map_map]
  congr 1

theorem transposeConfiguration_monotone : Monotone (latticeConfigurationIsoHomeomorph latticeTransposeIso) := by
  intro ω η h e
  simp only [latticeConfigurationIsoHomeomorph_apply]
  exact h _

end
end PottsContinuity.PlanarTopology
