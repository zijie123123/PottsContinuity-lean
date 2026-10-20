module

public import PottsContinuity.FKC.Medial.WholePlaneDualConfiguration
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4Records
noncomputable section

/-- Coordinate-preserving identification of the two imported axis carriers. -/
def latticeAxisEquiv : FKC.Medial.LatticeAxis ≃ PD.FK.Medial.LatticeAxis where
  toFun a := match a with | .horizontal => .horizontal | .vertical => .vertical
  invFun a := match a with | .horizontal => .horizontal | .vertical => .vertical
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-- The FKC and all-q PD libraries use the same normalized geometric bonds. -/
def latticeBondEquiv : FKC.Medial.LatticeBond ≃ PD.FK.Medial.LatticeBond where
  toFun b := ⟨b.base,latticeAxisEquiv b.axis⟩
  invFun b := ⟨b.base,latticeAxisEquiv.symm b.axis⟩
  left_inv b := by cases b with | mk base axis => cases axis <;> rfl
  right_inv b := by cases b with | mk base axis => cases axis <;> rfl

@[simp] theorem latticeBondEquiv_source (b : FKC.Medial.LatticeBond) :
    (latticeBondEquiv b).source = b.source := rfl

@[simp] theorem latticeBondEquiv_target (b : FKC.Medial.LatticeBond) :
    (latticeBondEquiv b).target = b.target := by
  cases b with | mk base axis => cases axis <;> rfl

@[simp] theorem latticeBondEquiv_toSym2 (b : FKC.Medial.LatticeBond) :
    (latticeBondEquiv b).toSym2 = b.toSym2 := by
  simp only [PD.FK.Medial.LatticeBond.toSym2,FKC.Medial.LatticeBond.toSym2,
    latticeBondEquiv_source,latticeBondEquiv_target]

@[simp] theorem latticeBondEquiv_dualBondOfPrimal (b : FKC.Medial.LatticeBond) :
    latticeBondEquiv (FKC.Medial.dualBondOfPrimal b) =
      PD.FK.Medial.dualBondOfPrimal (latticeBondEquiv b) := by
  cases b with | mk base axis => cases axis <;> rfl

@[simp] theorem latticeBondEquiv_primalBondOfDual (b : FKC.Medial.LatticeBond) :
    latticeBondEquiv (FKC.Medial.primalBondOfDual b) =
      PD.FK.Medial.primalBondOfDual (latticeBondEquiv b) := by
  cases b with | mk base axis => cases axis <;> rfl

end
end PottsContinuity.Thm4Records
