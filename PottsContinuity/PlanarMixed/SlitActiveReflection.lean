module

public import PottsContinuity.PlanarMixed.SlitReflectedCarrier
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Star

/-! The repaired domain inclusion after freezing all boundary-internal primal
arc bonds OPEN, so their crossing dual bonds are closed and absent. The bare
sampled carrier fails inclusion; the actual active carrier satisfies it. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.FK.Medial

/-- Original nearest-neighbour bonds internal to A or K(y,infinity). -/
def SlitPrewiredBond (x y : ℤ) (e : LatticeBond) : Prop :=
  (e.axis = .horizontal ∧ e.base.2 = 0 ∧ e.base.1 < x) ∨
    (e.axis = .vertical ∧ e.base.1 = x ∧ y ≤ e.base.2)

/-- Sampled source bonds after the already prewired arc bonds are frozen. -/
def SlitActiveBond (x y : ℤ) (e : LatticeBond) : Prop :=
  SlitRetainedBond x y e ∧ ¬ SlitPrewiredBond x y e

/-- Exact reflected active carrier, with no guessed boundary completion. -/
def SlitReflectedActiveBond (x y : ℤ) (e : LatticeBond) : Prop :=
  SlitActiveBond x y (slitReflectedBondInv x e)

/-- The corrected image carrier can be read directly on its original integer
coordinates. Boundary-internal source bonds remove precisely the extra
horizontal crossing bonds and the right part of the vertical bottom row. -/
theorem slitReflectedActiveBond_iff (x y : ℤ) (e : LatticeBond) :
    SlitReflectedActiveBond x y e ↔
      match e.axis with
      | .horizontal => 1 ≤ e.base.2 ∧ ¬ (e.base.1 = x-1 ∧ y < e.base.2)
      | .vertical => 0 ≤ e.base.2 ∧ ¬ (e.base.1 = x ∧ y < e.base.2) ∧
          ¬ (x ≤ e.base.1 ∧ e.base.2 = 0) := by
  rcases e with ⟨⟨a,b⟩,ax⟩
  cases ax <;>
    simp [SlitReflectedActiveBond, SlitActiveBond, SlitRetainedBond,
      SlitPrewiredBond, slitReflectedBondInv] <;> omega

/-- The repaired deterministic source inclusion holds on EVERY active bond. -/
theorem slitReflectedActiveBond_subset_retained (x y : ℤ) (e : LatticeBond) :
    SlitReflectedActiveBond x y e → SlitRetainedBond x y e := by
  rw [slitReflectedActiveBond_iff]
  rcases e with ⟨⟨a,b⟩,ax⟩
  cases ax <;> simp [SlitRetainedBond] <;> omega

/-- All actual unbounded slit bonds, with other original lattice vertices
retained as isolated vertices. This is an edge-carrier representation of D. -/
def slitRetainedBondGraph (x y : ℤ) : SimpleGraph LatticeVertex :=
  SimpleGraph.fromEdgeSet {s | ∃ e : LatticeBond, SlitRetainedBond x y e ∧ e.toSym2 = s}

end PottsContinuity.PlanarMixed
