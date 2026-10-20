module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushDefinitions
public import PottsContinuity.Thm3.Push.RectangleBandEventBridge

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open RSW PD.FK PD.Duality
noncomputable section

theorem nativeSideCrossingProbability_eq_rectangleBand
    (q : Set.Ici (1:ℝ)) (m : ℕ) (hm : 1 ≤ m) :
    nativeSideCrossingProbability q m =
    (measure (rectangleGraph (-16*(m:ℤ)-1,0) (32*m+1) (15*m))
      (selfDualParameters q)
      (BoundaryCondition.wired {z : RectangleVertex (-16*(m:ℤ)-1,0) (32*m+1) (15*m) |
        z.val.1 = -16*(m:ℤ)-1 ∨ z.val.1 = 16*(m:ℤ) ∨ z.val.2 = 15*(m:ℤ)})
      (Push.rectangleBandConnectionEvent (-16*(m:ℤ)-1,0) (32*m+1)
        (4*m-1) (15*m) (by omega))).toReal := by
  have hbox : PD.FK.latticeRectangle (-16*(m:ℤ)-1,0) (32*m+1) (15*m) =
      nativeSideRectangle m := by
    ext z
    rw [PD.FK.mem_latticeRectangle]
    simp only [nativeSideRectangle,PottsContinuity.latticeRectangle,
      Finset.mem_product,Finset.mem_Icc]
    omega
  have hr : -16*(m:ℤ)-1 + ((32*m+1:ℕ):ℤ) = 16*(m:ℤ) := by omega
  have hh : (0:ℤ) + ((15*m:ℕ):ℤ) = 15*(m:ℤ) := by omega
  have hb : (0:ℤ) + ((4*m-1:ℕ):ℤ) = ((4*m-1:ℕ):ℤ) := by omega
  have hp := Push.rectangleBand_crossing_probability (-16*(m:ℤ)-1,0)
    (32*m+1) (15*m) (4*m-1) (by omega) (selfDualParameters q)
  let F (V : Finset LatticeVertex) := finiteBoundaryEventProbability V (selfDualParameters q)
    (BoundaryCondition.wired {v | v.val.1=-16*(m:ℤ)-1 ∨
      v.val.1=16*(m:ℤ) ∨ v.val.2=15*(m:ℤ)})
    (horizontalCrossing V (-16*(m:ℤ)-1) (16*(m:ℤ)) 0 (4*m-1:ℕ))
  have hF := congrArg F hbox
  exact hF.symm.trans (by simpa only [hr,hh,hb] using hp)

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
