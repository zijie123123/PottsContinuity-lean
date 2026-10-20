module

public import PottsContinuity.PlanarTopology.AlphaCoreReflections

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Half-turn about the physical origin in integer dual face coordinates. -/
abbrev alphaCoreReflectionBothIso : PD.squareLattice ≃g PD.squareLattice :=
  alphaCoreReflectionXIso.trans alphaCoreReflectionYIso

theorem alphaCoreReflectionBothIso_box (c v : LatticeVertex) (r : ℕ) :
    alphaCoreReflectionBothIso v ∈ latticeBox (alphaCoreReflectionBothIso c) r ↔ v ∈ latticeBox c r :=
  latticeBox_iso_trans _ _ alphaCoreReflectionXIso_box alphaCoreReflectionYIso_box c v r

theorem alphaCoreReflectionXIso_symm_apply (z : LatticeVertex) :
    alphaCoreReflectionXIso.symm z = alphaCoreReflectionXIso z := by
  change (-(z.1- -1),z.2-0) = (-z.1+ -1,z.2+0)
  ext <;> dsimp <;> omega

theorem alphaCoreLeftTargets_x_map (k : ℕ) (u : LatticeVertex) :
    alphaCoreReflectionXIso u ∈ alphaCoreLeftTargets k ↔ u ∈ alphaCoreRightTargets k := by
  rw [← alphaCoreReflectionXIso_symm_apply]
  exact alphaCoreLeftTargets_x_reflection k u

theorem alphaCoreRightTargets_x_map (k : ℕ) (u : LatticeVertex) :
    alphaCoreReflectionXIso u ∈ alphaCoreRightTargets k ↔ u ∈ alphaCoreLeftTargets k := by
  rw [← alphaCoreReflectionXIso_symm_apply]
  exact alphaCoreRightTargets_x_reflection k u

theorem alphaCoreLeftTargets_y_map (k : ℕ) (u : LatticeVertex) :
    alphaCoreReflectionYIso u ∈ alphaCoreLeftTargets k ↔ u ∈ alphaCoreLeftTargets k := by
  simp only [alphaCoreLeftTargets,Set.mem_ofPred_eq]
  change ((-65*(k : ℤ) ≤ u.1+0 ∧ u.1+0 ≤ -(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ -u.2+ -1 ∧ -u.2+ -1 ≤ 64*(k : ℤ)-1) ∧
    (u.1+0 = -65*(k : ℤ) ∨ -u.2+ -1 = -64*(k : ℤ) ∨ -u.2+ -1 = 64*(k : ℤ)-1)) ↔ _
  omega

theorem alphaCoreRightTargets_y_map (k : ℕ) (u : LatticeVertex) :
    alphaCoreReflectionYIso u ∈ alphaCoreRightTargets k ↔ u ∈ alphaCoreRightTargets k := by
  simp only [alphaCoreRightTargets,Set.mem_ofPred_eq]
  change (((k : ℤ) ≤ u.1+0 ∧ u.1+0 ≤ 65*(k : ℤ)-1) ∧
    (-64*(k : ℤ) ≤ -u.2+ -1 ∧ -u.2+ -1 ≤ 64*(k : ℤ)-1) ∧
    (u.1+0 = 65*(k : ℤ)-1 ∨ -u.2+ -1 = -64*(k : ℤ) ∨ -u.2+ -1 = 64*(k : ℤ)-1)) ↔ _
  omega

/-- Map a confined walk using a genuine symmetry of its complete core box. -/
theorem alpha_core_bounds_map (k : ℕ) (e : PD.squareLattice ≃g PD.squareLattice)
    (he : ∀ z : LatticeVertex,
      (-65*(k : ℤ) ≤ z.1 ∧ z.1 ≤ 65*(k : ℤ)-1 ∧ -64*(k : ℤ) ≤ z.2 ∧ z.2 ≤ 64*(k : ℤ)-1) →
      (-65*(k : ℤ) ≤ (e z).1 ∧ (e z).1 ≤ 65*(k : ℤ)-1 ∧
        -64*(k : ℤ) ≤ (e z).2 ∧ (e z).2 ≤ 64*(k : ℤ)-1))
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathIn p (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1)) :
    kstPathIn (p.map e.toHom) (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1) := by
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact he w (hp w hw)

end
end PottsContinuity.PlanarTopology
