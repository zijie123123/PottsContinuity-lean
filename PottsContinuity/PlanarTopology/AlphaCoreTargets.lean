module

public import PottsContinuity.PlanarTopology.AlphaTargetDualPorts
public import PottsContinuity.PlanarTopology.RectangleDualCoreReachability
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK

/-- Left three-piece target after contracting pendant alpha-dual ports. -/
def alphaCoreLeftTargets (k : ℕ) : Set LatticeVertex :=
  {z | (-65*(k : ℤ) ≤ z.1 ∧ z.1 ≤ -(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ z.2 ∧ z.2 ≤ 64*(k : ℤ)-1) ∧
    (z.1 = -65*(k : ℤ) ∨ z.2 = -64*(k : ℤ) ∨ z.2 = 64*(k : ℤ)-1)}

/-- Right three-piece target in the same literal interior face box. -/
def alphaCoreRightTargets (k : ℕ) : Set LatticeVertex :=
  {z | ((k : ℤ) ≤ z.1 ∧ z.1 ≤ 65*(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ z.2 ∧ z.2 ≤ 64*(k : ℤ)-1) ∧
    (z.1 = 65*(k : ℤ)-1 ∨ z.2 = -64*(k : ℤ) ∨ z.2 = 64*(k : ℤ)-1)}

/-- Every original left exterior port contracts to the stated original
interior target, with the central gap retained exactly. -/
theorem alpha_left_port_core_target (k : ℕ) (hk : 1 ≤ k) (z : LatticeVertex)
    (hz : z ∈ alphaLeftDualPorts k) :
    rectangleCoreClamp (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)
      (by omega) (by omega) z ∈ alphaCoreLeftTargets k := by
  have hb := rectangleCoreClamp_bounds (-65*(k : ℤ),-64*(k : ℤ))
    (130*k) (128*k) (by omega) (by omega) z
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hb
  have hzx : z.1 ≤ -(k : ℤ)-1 := by rcases hz with hz | hz <;> omega
  have hcoreX : (rectangleCoreClamp (-65*(k : ℤ),-64*(k : ℤ))
      (130*k) (128*k) (by omega) (by omega) z).1 ≤ -(k : ℤ)-1 := by
    change max (-65*(k : ℤ)) (min (-65*(k : ℤ)+(130*k : ℕ)-1) z.1) ≤ _
    exact max_le (by omega) ((min_le_right _ _).trans hzx)
  refine ⟨⟨hb.1,hcoreX⟩,⟨hb.2.2.1,by omega⟩,?_⟩
  rcases hz with hz | ⟨hy,_,_⟩
  · left
    change max (-65*(k : ℤ)) (min (-65*(k : ℤ)+(130*k : ℕ)-1) z.1) = _
    exact max_eq_left ((min_le_right _ _).trans (by omega))
  · rcases hy with hy | hy
    · right; left
      change max (-64*(k : ℤ)) (min (-64*(k : ℤ)+(128*k : ℕ)-1) z.2) = _
      exact max_eq_left ((min_le_right _ _).trans (by omega))
    · right; right
      change max (-64*(k : ℤ)) (min (-64*(k : ℤ)+(128*k : ℕ)-1) z.2) = _
      have hc : -64*(k : ℤ)+(128*k : ℕ)-1 = 64*(k : ℤ)-1 := by push_cast; ring
      rw [hc,min_eq_left (by omega),max_eq_right (by omega)]

/-- The right endpoint contracts to its exact half-open interior target. -/
theorem alpha_right_port_core_target (k : ℕ) (hk : 1 ≤ k) (z : LatticeVertex)
    (hz : z ∈ alphaRightDualPorts k) :
    rectangleCoreClamp (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)
      (by omega) (by omega) z ∈ alphaCoreRightTargets k := by
  have hb := rectangleCoreClamp_bounds (-65*(k : ℤ),-64*(k : ℤ))
    (130*k) (128*k) (by omega) (by omega) z
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hb
  have hzx : (k : ℤ) ≤ z.1 := by rcases hz with hz | hz <;> omega
  have hcoreX : (k : ℤ) ≤ (rectangleCoreClamp (-65*(k : ℤ),-64*(k : ℤ))
      (130*k) (128*k) (by omega) (by omega) z).1 := by
    change (k : ℤ) ≤ max (-65*(k : ℤ)) (min (-65*(k : ℤ)+(130*k : ℕ)-1) z.1)
    exact (le_min (by push_cast; omega) hzx).trans (le_max_right _ _)
  refine ⟨⟨hcoreX,by omega⟩,⟨hb.2.2.1,by omega⟩,?_⟩
  rcases hz with hz | ⟨hy,_,_⟩
  · left
    change max (-65*(k : ℤ)) (min (-65*(k : ℤ)+(130*k : ℕ)-1) z.1) = _
    have hc : -65*(k : ℤ)+(130*k : ℕ)-1 = 65*(k : ℤ)-1 := by push_cast; ring
    rw [hc,min_eq_left (by omega),max_eq_right (by omega)]
  · rcases hy with hy | hy
    · right; left
      change max (-64*(k : ℤ)) (min (-64*(k : ℤ)+(128*k : ℕ)-1) z.2) = _
      exact max_eq_left ((min_le_right _ _).trans (by omega))
    · right; right
      change max (-64*(k : ℤ)) (min (-64*(k : ℤ)+(128*k : ℕ)-1) z.2) = _
      have hc : -64*(k : ℤ)+(128*k : ℕ)-1 = 64*(k : ℤ)-1 := by push_cast; ring
      rw [hc,min_eq_left (by omega),max_eq_right (by omega)]

end PottsContinuity.PlanarTopology
