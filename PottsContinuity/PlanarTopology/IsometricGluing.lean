module

public import PottsContinuity.PlanarTopology.IsometricEvents

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- A finite isometric gluing can be padded by cyclic repetition of its
actual factors. Every repeated factor is one of the original factors. -/
theorem isometric_gluing_pad {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    {A B : Set LatticeConfiguration}
    (hglue : ∃ e : Fin k → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' A) ⊆ B) :
    ∃ e : Fin l → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v r, e j v ∈ latticeBox (e j c) r ↔ v ∈ latticeBox c r) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' A) ⊆ B := by
  obtain ⟨f,hf,hglue⟩ := hglue
  let e : Fin l → (PD.squareLattice ≃g PD.squareLattice) :=
    fun j => f ⟨j.val % k,Nat.mod_lt _ (by omega)⟩
  refine ⟨e,fun j => hf _,?_⟩
  intro ω hω
  apply hglue
  apply Set.mem_iInter.mpr
  intro j
  have hj := Set.mem_iInter.mp hω (⟨j.val,by omega⟩ : Fin l)
  have he : e ⟨j.val,by omega⟩ = f j := by
    dsimp [e]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
  rwa [he] at hj

/-- An isometric pullback of a source event has a gluing to the same target:
compose every original factor with the inverse of the event isometry. -/
theorem isometric_gluing_iso_preimage {k : ℕ} {A B : Set LatticeConfiguration}
    (r : PD.squareLattice ≃g PD.squareLattice)
    (hr : ∀ c v s, r v ∈ latticeBox (r c) s ↔ v ∈ latticeBox c s)
    (hglue : ∃ e : Fin k → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v s, e j v ∈ latticeBox (e j c) s ↔ v ∈ latticeBox c s) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹' A) ⊆ B) :
    ∃ e : Fin k → (PD.squareLattice ≃g PD.squareLattice),
      (∀ j c v s, e j v ∈ latticeBox (e j c) s ↔ v ∈ latticeBox c s) ∧
      (⋂ j, latticeConfigurationIsoHomeomorph (e j) ⁻¹'
        (latticeConfigurationIsoHomeomorph r ⁻¹' A)) ⊆ B := by
  obtain ⟨f,hf,hglue⟩ := hglue
  refine ⟨fun j => (f j).trans r.symm,
    fun j => latticeBox_iso_trans (f j) r.symm (hf j) (latticeBox_iso_symm r hr),?_⟩
  intro ω hω
  apply hglue
  apply Set.mem_iInter.mpr
  intro j
  have hj := Set.mem_iInter.mp hω j
  change latticeConfigurationIsoHomeomorph r
    (latticeConfigurationIsoHomeomorph ((f j).trans r.symm) ω) ∈ A at hj
  rw [← latticeConfigurationIsoHomeomorph_trans_apply] at hj
  have he : ((f j).trans r.symm).trans r = f j := by
    apply DFunLike.ext
    intro v
    exact r.apply_symm_apply _
  rwa [he] at hj

end
end PottsContinuity.PlanarTopology
