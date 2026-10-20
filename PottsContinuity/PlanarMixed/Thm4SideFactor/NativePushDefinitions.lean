module

public import PottsContinuity.Thm3.Push.UnconditionalPush
public import PottsContinuity.Thm3.Push.AsymmetricRectangleComparison

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open RSW PD.FK PD.RCInfinite
noncomputable section

def nativeSideRectangle (m : ℕ) : Finset LatticeVertex :=
  PottsContinuity.latticeRectangle (-16*(m:ℤ)-1) (16*(m:ℤ)) 0 (15*(m:ℤ))

def nativeSideBoundary (m : ℕ) : BoundaryCondition (nativeSideRectangle m : Set LatticeVertex) :=
  BoundaryCondition.wired {v | v.val.1 = -16*(m:ℤ)-1 ∨
    v.val.1 = 16*(m:ℤ) ∨ v.val.2 = 15*(m:ℤ)}

def nativeSideCrossingEvent (m : ℕ) :=
  horizontalCrossing (nativeSideRectangle m) (-16*(m:ℤ)-1) (16*(m:ℤ)) 0 (4*m-1:ℕ)

def nativeSideCrossingProbability (q : Set.Ici (1:ℝ)) (m : ℕ) : ℝ :=
  finiteBoundaryEventProbability (nativeSideRectangle m) (selfDualParameters q)
    (nativeSideBoundary m) (nativeSideCrossingEvent m)


end
end PottsContinuity.PlanarMixed.Thm4SideFactor
