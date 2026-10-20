module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightSourceBonds
public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushBridge

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial DualityExt Thm4Side
noncomputable section

def rightNativeToHostDual (m : ℕ) :
    RectangleVertex (-16*(m:ℤ)-1,0) (32*m+1) (15*m) ↪
      RectangleDualVertex (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ))
        (2*(16*m+1)) (2*(16*m+1)) where
  toFun z := ⟨((m:ℤ)+z.val.2,z.val.1),by
    have hz := (PD.FK.mem_latticeRectangle _ z.val _ _).mp z.property
    rw [rectangleDualExpanded,PD.FK.mem_latticeRectangle]
    push_cast at hz ⊢
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro z v he
    apply Subtype.ext
    have hv := congrArg (fun u : RectangleDualVertex
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)) => u.val) he
    ext
    · exact congrArg Prod.snd hv
    · have h := congrArg Prod.fst hv
      dsimp at h
      omega

def rightNativeDualBond (m : ℕ) (d : LatticeBond) : LatticeBond :=
  ⟨((m:ℤ)+d.base.2,d.base.1),match d.axis with | .horizontal => .vertical | .vertical => .horizontal⟩

theorem rightNativeDualBond_pair (m : ℕ) (d : LatticeBond) :
    (rightNativeDualBond m d).toSym2 =
      Sym2.map (fun z : LatticeVertex => ((m:ℤ)+z.2,z.1)) d.toSym2 := by
  cases ha : d.axis <;>
    simp [rightNativeDualBond,LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,ha,add_assoc]

theorem rightNative_primal_supported (m : ℕ) (d : LatticeBond)
    (hs : d.source ∈ PD.FK.latticeRectangle (-16*(m:ℤ)-1,0) (32*m+1) (15*m))
    (ht : d.target ∈ PD.FK.latticeRectangle (-16*(m:ℤ)-1,0) (32*m+1) (15*m))
    (hn : ¬ ((d.source.1 = -16*(m:ℤ)-1 ∨ d.source.1 = (16*m:ℤ) ∨ d.source.2 = (15*m:ℤ)) ∧
      (d.target.1 = -16*(m:ℤ)-1 ∨ d.target.1 = (16*m:ℤ) ∨ d.target.2 = (15*m:ℤ)))) :
    (primalBondOfDual (rightNativeDualBond m d)).source ∈
      PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m) ∧
    (primalBondOfDual (rightNativeDualBond m d)).target ∈
      PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m) := by
  rw [PD.FK.mem_latticeRectangle] at hs ht
  constructor <;> rw [PD.FK.mem_latticeRectangle]
  all_goals
    cases ha : d.axis <;>
      simp only [rightNativeDualBond,primalBondOfDual,LatticeBond.source,LatticeBond.target,ha] at hs ht hn ⊢ <;>
      push_cast at hs ht hn ⊢ <;> omega

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
