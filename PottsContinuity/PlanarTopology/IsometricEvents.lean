module

public import PottsContinuity.PlanarTopology.KSTBridgeBottomEvent

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Configuration transport composes in the same order as graph isomorphisms. -/
theorem latticeConfigurationIsoHomeomorph_trans_apply
    (e f : PD.squareLattice ≃g PD.squareLattice) (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph (e.trans f) ω =
      latticeConfigurationIsoHomeomorph f (latticeConfigurationIsoHomeomorph e ω) := by
  funext b
  simp only [latticeConfigurationIsoHomeomorph_apply]
  congr 1
  apply Subtype.ext
  change Sym2.map (fun z => e.symm (f.symm z)) b.val =
    Sym2.map e.symm (Sym2.map f.symm b.val)
  rw [Sym2.map_map]
  rfl

/-- Pullbacks by lattice isometries preserve finite-coordinate dependence. -/
theorem isCylinder_iso_preimage (e : PD.squareLattice ≃g PD.squareLattice)
    {A : Set LatticeConfiguration} (hA : PD.RCInfinite.IsCylinder A) :
    PD.RCInfinite.IsCylinder (latticeConfigurationIsoHomeomorph e ⁻¹' A) := by
  classical
  obtain ⟨F,hF⟩ := hA
  refine ⟨F.map e.symm.mapEdgeSet.toEmbedding,?_⟩
  intro ω η hωη
  apply hF
  intro b hb
  simp only [latticeConfigurationIsoHomeomorph_apply]
  exact hωη _ (Finset.mem_map.mpr ⟨b,hb,rfl⟩)

/-- Isometric pullbacks of increasing events are increasing. -/
theorem isUpperSet_iso_preimage (e : PD.squareLattice ≃g PD.squareLattice)
    {A : Set LatticeConfiguration} (hA : IsUpperSet A) :
    IsUpperSet (latticeConfigurationIsoHomeomorph e ⁻¹' A) := by
  intro ω η hωη hω
  apply hA _ hω
  intro b
  simp only [latticeConfigurationIsoHomeomorph_apply]
  exact hωη _

/-- Box preservation is closed under chronological composition. -/
theorem latticeBox_iso_trans (e f : PD.squareLattice ≃g PD.squareLattice)
    (he : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (hf : ∀ c v r, f v ∈ latticeBox (f c) r ↔ v ∈ latticeBox c r) :
    ∀ c v r, (e.trans f) v ∈ latticeBox ((e.trans f) c) r ↔ v ∈ latticeBox c r := by
  intro c v r
  exact (hf (e c) (e v) r).trans (he c v r)

/-- The inverse of a box-preserving lattice isomorphism also preserves boxes. -/
theorem latticeBox_iso_symm (e : PD.squareLattice ≃g PD.squareLattice)
    (he : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    ∀ c v r, e.symm v ∈ latticeBox (e.symm c) r ↔ v ∈ latticeBox c r := by
  intro c v r
  simpa only [e.apply_symm_apply] using (he (e.symm c) (e.symm v) r).symm

/-- The reused horizontal-coordinate reflection preserves the full box family. -/
theorem kstReflectionXIso_box (c v : LatticeVertex) (r : ℕ) :
    kstReflectionXIso v ∈ latticeBox (kstReflectionXIso c) r ↔ v ∈ latticeBox c r :=
  Infinite.mem_latticeBox_reflection_iff c v r

end
end PottsContinuity.PlanarTopology
