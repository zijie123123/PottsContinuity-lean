module

public import PottsContinuity.PlanarTopology.IsometricEvents

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Reflection in the horizontal coordinate axis, composed from reused isometries. -/
abbrev kstReflectionYIso : PD.squareLattice ≃g PD.squareLattice :=
  latticeTransposeIso.trans (kstReflectionXIso.trans latticeTransposeIso)

/-- The half-turn used for the fourth boundary alternative. -/
abbrev kstReflectionBothIso : PD.squareLattice ≃g PD.squareLattice :=
  kstReflectionXIso.trans kstReflectionYIso

theorem latticeTransposeIso_box (c v : LatticeVertex) (r : ℕ) :
    latticeTransposeIso v ∈ latticeBox (latticeTransposeIso c) r ↔ v ∈ latticeBox c r := by
  simp only [mem_latticeBox]
  change ((c.2-(r : ℤ) ≤ v.2 ∧ v.2 ≤ c.2+r) ∧ c.1-r ≤ v.1 ∧ v.1 ≤ c.1+r) ↔ _
  omega

theorem kstReflectionYIso_box (c v : LatticeVertex) (r : ℕ) :
    kstReflectionYIso v ∈ latticeBox (kstReflectionYIso c) r ↔ v ∈ latticeBox c r :=
  latticeBox_iso_trans latticeTransposeIso _ latticeTransposeIso_box
    (latticeBox_iso_trans kstReflectionXIso latticeTransposeIso kstReflectionXIso_box
      latticeTransposeIso_box) c v r

theorem kstReflectionBothIso_box (c v : LatticeVertex) (r : ℕ) :
    kstReflectionBothIso v ∈ latticeBox (kstReflectionBothIso c) r ↔ v ∈ latticeBox c r :=
  latticeBox_iso_trans kstReflectionXIso kstReflectionYIso kstReflectionXIso_box
    kstReflectionYIso_box c v r

/-- Horizontal-axis reflection preserves each literal bridge target. -/
theorem kstBridgeLeft_y_reflection_iff (m : ℕ) (u : LatticeVertex) :
    kstBridgeLeft m (kstReflectionYIso u) ↔ kstBridgeLeft m u := by
  change (12*|u.1| ≤ 13*(m : ℤ) ∧ |-u.2| ≤ (m : ℤ) ∧
    12*u.1 ≤ -(m : ℤ) ∧ (|-u.2| = (m : ℤ) ∨ u.1 = -((13*m/12 : ℕ) : ℤ))) ↔ _
  simp only [abs_neg,kstBridgeLeft]

theorem kstBridgeRight_y_reflection_iff (m : ℕ) (u : LatticeVertex) :
    kstBridgeRight m (kstReflectionYIso u) ↔ kstBridgeRight m u := by
  change (12*|u.1| ≤ 13*(m : ℤ) ∧ |-u.2| ≤ (m : ℤ) ∧
    (m : ℤ) ≤ 12*u.1 ∧ (|-u.2| = (m : ℤ) ∨ u.1 = ((13*m/12 : ℕ) : ℤ))) ↔ _
  simp only [abs_neg,kstBridgeRight]

/-- Isometries preserving both absolute coordinates preserve the full original
bridge rectangle support of a mapped walk. -/
theorem kst_bridge_bounds_map_of_abs_coordinates
    (e : PD.squareLattice ≃g PD.squareLattice)
    (he : ∀ z : LatticeVertex, |(e z).1| = |z.1| ∧ |(e z).2| = |z.2|)
    (m : ℕ) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : ∀ z ∈ p.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ)) :
    ∀ z ∈ (p.map e.toHom).support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ) := by
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  change 12*|(e w).1| ≤ 13*(m : ℤ) ∧ |(e w).2| ≤ (m : ℤ)
  rw [(he w).1,(he w).2]
  exact hp w hw

end
end PottsContinuity.PlanarTopology
