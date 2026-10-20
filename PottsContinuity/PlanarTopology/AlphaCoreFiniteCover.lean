module

public import PottsContinuity.PlanarTopology.AlphaCoreCoverGluing

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial BD12
noncomputable section

/-- Exact odd-core bridge cover and long-crossing certificate. -/
theorem alpha_core_bridge_finite_cover (a : ℕ) (ha : 1 ≤ a) :
    ∃ S : Fin 2000 → Set LatticeConfiguration,
      (∀ i, PD.RCInfinite.IsCylinder (S i) ∧ IsUpperSet (S i)) ∧
      (alphaCoreBridge a ⊆ ⋃ i, S i) ∧
      (∀ i, ∃ e : Fin 2000 → (PD.squareLattice ≃g PD.squareLattice),
        (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
        (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i) ⊆
          horizontalRectangle (-512*(a : ℤ)-1,-64*(a : ℤ)) (1024*a+1) (128*a-1)) := by
  let idx : Fin 2000 → Fin 5 := fun i => ⟨i.val % 5,Nat.mod_lt _ (by decide)⟩
  let S : Fin 2000 → Set LatticeConfiguration := fun i => alphaCoreCoverPiece a (idx i)
  refine ⟨S,fun i => ⟨alphaCoreCoverPiece_isCylinder a (idx i),
    alphaCoreCoverPiece_isUpperSet a (idx i)⟩,?_,?_⟩
  · intro ω hω
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (alpha_core_bridge_five_cover a ha hω)
    let i : Fin 2000 := ⟨j.val,by omega⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    have hi : idx i = j := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt j.isLt
    change ω ∈ alphaCoreCoverPiece a (idx i)
    rwa [hi]
  · intro i
    exact alpha_core_cover_piece_gluing a ha (idx i)

/-- Arm absence is covered by genuine increasing dual-cylinder candidates;
each candidate has the exact long-crossing gluing certificate. -/
theorem kst_arm_complement_dual_finite_cover (k : ℕ) (hk : 1 ≤ k) :
    ∃ S : Fin 2000 → Set LatticeConfiguration,
      (∀ i, PD.RCInfinite.IsCylinder (S i) ∧ IsUpperSet (S i)) ∧
      ((kstArm (64*k))ᶜ ⊆ wholePlaneDualConfigurationHomeomorph ⁻¹' (⋃ i, S i)) ∧
      (∀ i, ∃ e : Fin 2000 → (PD.squareLattice ≃g PD.squareLattice),
        (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
        (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i) ⊆
          horizontalRectangle (-512*(k : ℤ)-1,-64*(k : ℤ)) (1024*k+1) (128*k-1)) := by
  obtain ⟨S,hS,hcover,hglue⟩ := alpha_core_bridge_finite_cover k hk
  exact ⟨S,hS,fun ω hω => hcover (kstArm_compl_subset_dual_core_bridge k hk hω),hglue⟩

end
end PottsContinuity.PlanarTopology
