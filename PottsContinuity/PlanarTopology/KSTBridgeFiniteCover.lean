module

public import PottsContinuity.PlanarTopology.KSTBridgeCoverGluing

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Complete increasing cylinder cover and deterministic gluing at every
positive integral beta scale. All five genuine candidates are repeated to
match the common 2000-event form. -/
theorem kst_bridge_finite_cover_multiple12 (a : ℕ) (ha : 1 ≤ a) :
    ∃ S : Fin 2000 → Set LatticeConfiguration,
      (∀ i, PD.RCInfinite.IsCylinder (S i) ∧ IsUpperSet (S i)) ∧
      (kstBridge (12*a) ⊆ ⋃ i, S i) ∧
      (∀ i, ∃ e : Fin 2000 → (PD.squareLattice ≃g PD.squareLattice),
        (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
        (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i) ⊆
          horizontalRectangle (-8*((12*a : ℕ) : ℤ),-((12*a : ℕ) : ℤ)) (16*(12*a)) (2*(12*a))) := by
  let idx : Fin 2000 → Fin 5 := fun i => ⟨i.val % 5,Nat.mod_lt _ (by decide)⟩
  let S : Fin 2000 → Set LatticeConfiguration := fun i => kstBridgeCoverPiece a (idx i)
  refine ⟨S,fun i => ⟨kstBridgeCoverPiece_isCylinder a (idx i),
    kstBridgeCoverPiece_isUpperSet a (idx i)⟩,?_,?_⟩
  · intro ω hω
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (kst_bridge_five_cover a hω)
    let i : Fin 2000 := ⟨j.val,by omega⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    have hi : idx i = j := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt j.isLt
    change ω ∈ kstBridgeCoverPiece a (idx i)
    rwa [hi]
  · intro i
    have hstart : (-8*((12*a : ℕ) : ℤ),-((12*a : ℕ) : ℤ)) =
        (-96*(a : ℤ),-12*(a : ℤ)) := by
      push_cast
      apply Prod.ext <;> dsimp <;> ring
    have h16 : 16*(12*a) = 192*a := by omega
    have h2 : 2*(12*a) = 24*a := by omega
    rw [hstart,h16,h2]
    exact kst_bridge_cover_piece_gluing a ha (idx i)

/-- The exact finite bridge cover used in `BD12.KSTBridgeCoverExport`. This includes
cylinder and upper-set properties, the complete cover, literal original rectangle events,
and 2000 box-preserving gluing factors for every candidate. -/
theorem kst_bridge_finite_cover (m : ℕ) (hm : 192 ∣ m) (hmpos : 1 ≤ m) :
    ∃ S : Fin 2000 → Set LatticeConfiguration,
      (∀ i, PD.RCInfinite.IsCylinder (S i) ∧ IsUpperSet (S i)) ∧
      (kstBridge m ⊆ ⋃ i, S i) ∧
      (∀ i, ∃ e : Fin 2000 → (PD.squareLattice ≃g PD.squareLattice),
        (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
        (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i) ⊆
          horizontalRectangle (-8*(m : ℤ),-(m : ℤ)) (16*m) (2*m)) := by
  have hm12 : 12 ∣ m := dvd_trans (by decide : 12 ∣ 192) hm
  obtain ⟨a,rfl⟩ := hm12
  exact kst_bridge_finite_cover_multiple12 a (by omega)

end
end PottsContinuity.PlanarTopology
