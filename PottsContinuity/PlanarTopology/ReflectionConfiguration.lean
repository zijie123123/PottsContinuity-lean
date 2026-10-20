module

public import PottsContinuity.PlanarTopology.KSTBridgeBottomEvent
public import PottsContinuity.PlanarTopology.DualConfigurationTranslation

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- The normalized original bond under reflection of the horizontal coordinate. -/
def reflectionXLatticeBond (b : LatticeBond) : LatticeBond :=
  match b.axis with
  | .horizontal => ⟨(-b.base.1-1,b.base.2),.horizontal⟩
  | .vertical => ⟨(-b.base.1,b.base.2),.vertical⟩

theorem latticeConfigurationBondState_reflectionX (ω : LatticeConfiguration) (b : LatticeBond) :
    latticeConfigurationBondState (latticeConfigurationIsoHomeomorph kstReflectionXIso ω) b =
      latticeConfigurationBondState ω (reflectionXLatticeBond b) := by
  change latticeConfigurationIsoHomeomorph kstReflectionXIso ω (latticeBondEdge b) = _
  rw [latticeConfigurationIsoHomeomorph_apply]
  apply congrArg ω
  apply Subtype.ext
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [reflectionXLatticeBond,latticeBondEdge,LatticeBond.toSym2,LatticeBond.source,
    LatticeBond.target,SimpleGraph.Iso.mapEdgeSet,SimpleGraph.Hom.mapEdgeSet,kstReflectionXIso,
    Infinite.latticeReflectionIso,Infinite.latticeReflection]; omega

/-- The face-base convention adds a fixed translation when the actual dual
transform is commuted past horizontal-coordinate reflection. -/
theorem wholePlaneDualConfiguration_reflectionX (ω : LatticeConfiguration) :
    wholePlaneDualConfigurationHomeomorph (latticeConfigurationIsoHomeomorph kstReflectionXIso ω) =
      edgeTranslate (-1,0) (latticeConfigurationIsoHomeomorph kstReflectionXIso
        (wholePlaneDualConfigurationHomeomorph ω)) := by
  funext e
  obtain ⟨b,rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState
    (wholePlaneDualConfigurationHomeomorph (latticeConfigurationIsoHomeomorph kstReflectionXIso ω)) b =
    latticeConfigurationBondState
      (edgeTranslate (-1,0) (latticeConfigurationIsoHomeomorph kstReflectionXIso
        (wholePlaneDualConfigurationHomeomorph ω))) b
  rw [wholePlaneDualConfigurationHomeomorph_bondState,latticeConfigurationBondState_reflectionX,
    latticeConfigurationBondState_translate,latticeConfigurationBondState_reflectionX,
    wholePlaneDualConfigurationHomeomorph_bondState]
  congr 2
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp only [reflectionXLatticeBond,primalBondOfDual,latticeTranslate,
    Prod.fst_neg,Prod.snd_neg,neg_neg,neg_zero] <;> congr 1 <;> ext <;> omega

theorem reflectionXConfiguration_twice (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph kstReflectionXIso
      (latticeConfigurationIsoHomeomorph kstReflectionXIso ω) = ω := by
  funext e
  obtain ⟨b,rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState
    (latticeConfigurationIsoHomeomorph kstReflectionXIso
      (latticeConfigurationIsoHomeomorph kstReflectionXIso ω)) b = latticeConfigurationBondState ω b
  rw [latticeConfigurationBondState_reflectionX,latticeConfigurationBondState_reflectionX]
  congr 1
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [reflectionXLatticeBond]

theorem reflectionXConfiguration_translate (a : LatticeVertex) (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph kstReflectionXIso (edgeTranslate a ω) =
      edgeTranslate (-a.1,a.2) (latticeConfigurationIsoHomeomorph kstReflectionXIso ω) := by
  funext e
  simp only [latticeConfigurationTranslate_apply,latticeConfigurationIsoHomeomorph_apply]
  congr 1
  apply Subtype.ext
  simp only [SimpleGraph.Iso.mapEdgeSet_apply,SimpleGraph.Hom.mapEdgeSet_coe,Sym2.map_map]
  congr 1
  funext z
  ext <;> simp [kstReflectionXIso,Infinite.latticeReflectionIso,Infinite.latticeReflection,
    latticeTranslationIso,latticeTranslate,add_comm]

theorem reflectionXConfiguration_monotone : Monotone (latticeConfigurationIsoHomeomorph kstReflectionXIso) := by
  intro ω η h e
  simp only [latticeConfigurationIsoHomeomorph_apply]
  exact h _

end
end PottsContinuity.PlanarTopology
