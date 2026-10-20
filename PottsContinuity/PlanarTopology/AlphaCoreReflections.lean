module

public import PottsContinuity.PlanarTopology.KSTBridgeSymmetries
public import PottsContinuity.PlanarTopology.AlphaCoreTargets

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Reflection of integer face bases about the physical dual vertical axis. -/
abbrev alphaCoreReflectionXIso : PD.squareLattice ≃g PD.squareLattice :=
  kstReflectionXIso.trans (latticeTranslationIso (-1,0))

/-- Reflection of integer face bases about the physical dual horizontal axis. -/
abbrev alphaCoreReflectionYIso : PD.squareLattice ≃g PD.squareLattice :=
  kstReflectionYIso.trans (latticeTranslationIso (0,-1))

theorem alphaCoreReflectionXIso_box (c v : LatticeVertex) (r : ℕ) :
    alphaCoreReflectionXIso v ∈ latticeBox (alphaCoreReflectionXIso c) r ↔ v ∈ latticeBox c r :=
by
  simp only [mem_latticeBox]
  change (((-c.1 + -1)-(r : ℤ) ≤ -v.1 + -1 ∧ -v.1 + -1 ≤ (-c.1 + -1)+r) ∧
    (c.2+0)-r ≤ v.2+0 ∧ v.2+0 ≤ (c.2+0)+r) ↔ _
  omega

theorem alphaCoreReflectionYIso_box (c v : LatticeVertex) (r : ℕ) :
    alphaCoreReflectionYIso v ∈ latticeBox (alphaCoreReflectionYIso c) r ↔ v ∈ latticeBox c r :=
by
  simp only [mem_latticeBox]
  change (((c.1+0)-(r : ℤ) ≤ v.1+0 ∧ v.1+0 ≤ (c.1+0)+r) ∧
    (-c.2 + -1)-r ≤ -v.2 + -1 ∧ -v.2 + -1 ≤ (-c.2 + -1)+r) ↔ _
  omega

theorem alphaCoreLeftTargets_x_reflection (k : ℕ) (u : LatticeVertex) :
    alphaCoreReflectionXIso.symm u ∈ alphaCoreLeftTargets k ↔ u ∈ alphaCoreRightTargets k := by
  change ((-65*(k : ℤ) ≤ -(u.1- -1) ∧ -(u.1- -1) ≤ -(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ u.2-0 ∧ u.2-0 ≤ 64*(k : ℤ)-1) ∧
    (-(u.1- -1) = -65*(k : ℤ) ∨ u.2-0 = -64*(k : ℤ) ∨ u.2-0 = 64*(k : ℤ)-1)) ↔ _
  change _ ↔ (((k : ℤ) ≤ u.1 ∧ u.1 ≤ 65*(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ u.2 ∧ u.2 ≤ 64*(k : ℤ)-1) ∧
    (u.1 = 65*(k : ℤ)-1 ∨ u.2 = -64*(k : ℤ) ∨ u.2 = 64*(k : ℤ)-1))
  omega

theorem alphaCoreRightTargets_x_reflection (k : ℕ) (u : LatticeVertex) :
    alphaCoreReflectionXIso.symm u ∈ alphaCoreRightTargets k ↔ u ∈ alphaCoreLeftTargets k := by
  change (((k : ℤ) ≤ -(u.1- -1) ∧ -(u.1- -1) ≤ 65*(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ u.2-0 ∧ u.2-0 ≤ 64*(k : ℤ)-1) ∧
    (-(u.1- -1) = 65*(k : ℤ)-1 ∨ u.2-0 = -64*(k : ℤ) ∨ u.2-0 = 64*(k : ℤ)-1)) ↔ _
  change _ ↔ ((-65*(k : ℤ) ≤ u.1 ∧ u.1 ≤ -(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ u.2 ∧ u.2 ≤ 64*(k : ℤ)-1) ∧
    (u.1 = -65*(k : ℤ) ∨ u.2 = -64*(k : ℤ) ∨ u.2 = 64*(k : ℤ)-1))
  omega

/-- Both offset reflections preserve the literal core box. -/
theorem alphaCoreReflectionXIso_bounds (k : ℕ) (u : LatticeVertex) :
    (-65*(k : ℤ) ≤ (alphaCoreReflectionXIso.symm u).1 ∧
      (alphaCoreReflectionXIso.symm u).1 ≤ 65*(k : ℤ)-1 ∧
      -64*(k : ℤ) ≤ (alphaCoreReflectionXIso.symm u).2 ∧
      (alphaCoreReflectionXIso.symm u).2 ≤ 64*(k : ℤ)-1) ↔
    (-65*(k : ℤ) ≤ u.1 ∧ u.1 ≤ 65*(k : ℤ)-1 ∧
      -64*(k : ℤ) ≤ u.2 ∧ u.2 ≤ 64*(k : ℤ)-1) := by
  change (-65*(k : ℤ) ≤ -(u.1- -1) ∧ -(u.1- -1) ≤ 65*(k : ℤ)-1 ∧
    -64*(k : ℤ) ≤ u.2-0 ∧ u.2-0 ≤ 64*(k : ℤ)-1) ↔ _
  omega

end
end PottsContinuity.PlanarTopology
