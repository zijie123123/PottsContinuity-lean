module

public import PottsContinuity.PlanarMixed.Square.Consumers
public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import PottsContinuity.PD.Duality.LatticePorts
public import Mathlib.Tactic

/-! The corrected reflection on actual crossing bonds. All formulas use the
original normalized primal bond and its two actual adjacent dual cells. The
map swaps axes and its square translates upward; it is not an involution. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.FK.Medial

/-- Reflect the crossing dual bond by the corrected affine map and identify
its two resulting integer endpoints as a normalized primal bond. -/
def slitReflectedBond (x : ℤ) (e : LatticeBond) : LatticeBond :=
  match e.axis with
  | .horizontal => ⟨(2*x-1-e.base.1,e.base.2), .vertical⟩
  | .vertical => ⟨(2*x-1-e.base.1,e.base.2+1), .horizontal⟩

/-- The explicit inverse retains the different shifts on the two axes. -/
def slitReflectedBondInv (x : ℤ) (e : LatticeBond) : LatticeBond :=
  match e.axis with
  | .horizontal => ⟨(2*x-1-e.base.1,e.base.2-1), .vertical⟩
  | .vertical => ⟨(2*x-1-e.base.1,e.base.2), .horizontal⟩

theorem slitReflectedBondInv_apply (x : ℤ) (e : LatticeBond) :
    slitReflectedBondInv x (slitReflectedBond x e) = e := by
  rcases e with ⟨⟨a,b⟩,ax⟩
  cases ax <;> simp [slitReflectedBond, slitReflectedBondInv]

theorem slitReflectedBond_apply_inv (x : ℤ) (e : LatticeBond) :
    slitReflectedBond x (slitReflectedBondInv x e) = e := by
  rcases e with ⟨⟨a,b⟩,ax⟩
  cases ax <;> simp [slitReflectedBond, slitReflectedBondInv]

/-- A bijection of the full actual bond carrier, not a graph isomorphism of
the slit domains and not a duality-law assertion. -/
def slitReflectedBondEquiv (x : ℤ) : LatticeBond ≃ LatticeBond where
  toFun := slitReflectedBond x
  invFun := slitReflectedBondInv x
  left_inv := slitReflectedBondInv_apply x
  right_inv := slitReflectedBond_apply_inv x

end PottsContinuity.PlanarMixed
