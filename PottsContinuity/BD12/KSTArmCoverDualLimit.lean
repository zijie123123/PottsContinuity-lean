module

public import PottsContinuity.BD12.KSTBothBoundaryHypotheses
public import PottsContinuity.BD12.KSTEventRegularity
public import PottsContinuity.BD12.KSTFiniteAssociation
public import PottsContinuity.BD12.KSTCoverTransform
public import PottsContinuity.PlanarTopology.KSTArmDualCertificate
public import PottsContinuity.PlanarTopology.KSTBridgeSymmetries

/-! The probability consequence of the exact half-cell dual arm certificate.
The dual limit is explicit; no complementary same-centred bridge identity
is used. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK PD.FK.Medial PD.FK.Curves
noncomputable section

/-- KST first-relation (ii) from the actual dual boundary limit. The only dual-law
input is the exact pushforward identity, to be instantiated by whole-plane duality. -/
theorem kst_arm_cover_lower_bound_of_dualLimit (θ : Parameters) (bdy : Fin 2)
    (μ ν : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (hν : IsRCInfiniteVolumeLimit θ.toP θ.toQ bdy ν)
    (hmap : μ.map wholePlaneDualConfigurationHomeomorph = ν) (k : ℕ) (hk : 1 ≤ k) :
    kstCoverTransform (μ.real (horizontalRectangle (-64*(k : ℤ),-512*(k : ℤ)) (128*k) (1024*k))) ≤
      μ.real (kstArm (64*k)) := by
  let : IsProbabilityMeasure ν := hν.1
  let D := wholePlaneDualConfigurationHomeomorph
  let B := D.symm ⁻¹' (kstArm (64*k))ᶜ
  let L := PlanarTopology.alphaCoreLongRectangle k
  have hArm : MeasurableSet (kstArm (64*k)) := (kstArm_isOpen _).measurableSet
  have hB : MeasurableSet B := D.symm.continuous_toFun.measurable hArm.compl
  have hL : MeasurableSet L := (horizontalRectangle_isCylinder _ _ _).measurableSet
  obtain ⟨S, hS, hcover, hglue, hexclude⟩ := PlanarTopology.kst_arm_dual_cover_certificate k hk
  have hcover' : B ⊆ ⋃ i, S i := by
    intro ω hω
    have h := hcover hω
    simpa only [D, Set.mem_preimage, Homeomorph.apply_symm_apply] using h
  have hFKG := fun A C => @limit_measurable_positive_association θ bdy ν hν A C
  obtain ⟨i, hi⟩ := kst_finite_cover_square_root ν hFKG S
    (fun i => (hS i).1.measurableSet) (fun i => (hS i).2) hcover'
  obtain ⟨e, he, hglue⟩ := hglue i
  have hprod := kst_construction_of_kstCorridor ν hFKG
    (fun j => latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i)
    (fun j => (PlanarTopology.isCylinder_iso_preimage (e j) (hS i).1).measurableSet)
    (fun j => PlanarTopology.isUpperSet_iso_preimage (e j) (hS i).2) hglue
  have hsym (j : Fin 2000) :
      ν.real (latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i) = ν.real (S i) :=
    limit_isometry_preimage_real θ bdy ν hν (e j) (he j) (S i) (hS i).1.measurableSet
  simp only [hsym, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpre : D ⁻¹' B = (kstArm (64*k))ᶜ := by
    ext ω
    simp only [B, Set.mem_preimage, Homeomorph.symm_apply_apply]
  have hBmass : ν.real B = 1 - μ.real (kstArm (64*k)) := by
    rw [← hmap]
    change ((μ.map D) B).toReal = _
    rw [Measure.map_apply (f := (D : LatticeConfiguration → LatticeConfiguration)) D.continuous_toFun.measurable hB, hpre]
    change μ.real (kstArm (64*k))ᶜ = _
    rw [measureReal_compl hArm, probReal_univ]
  have hT : MeasurableSet (latticeConfigurationIsoHomeomorph PlanarTopology.latticeTransposeIso ⁻¹' L) :=
    (latticeConfigurationIsoHomeomorph_measurable _) hL
  have hDmass : μ.real (D ⁻¹' (latticeConfigurationIsoHomeomorph PlanarTopology.latticeTransposeIso ⁻¹' L)) = ν.real L := by
    change (μ (D ⁻¹' _)).toReal = _
    rw [← Measure.map_apply (f := (D : LatticeConfiguration → LatticeConfiguration)) D.continuous_toFun.measurable hT, hmap]
    exact limit_isometry_preimage_real θ bdy ν hν PlanarTopology.latticeTransposeIso
      PlanarTopology.latticeTransposeIso_box L hL
  have hshort := measureReal_mono (μ := μ) hexclude
  have hE : MeasurableSet (D ⁻¹' (latticeConfigurationIsoHomeomorph PlanarTopology.latticeTransposeIso ⁻¹' L)) :=
    D.continuous_toFun.measurable hT
  rw [measureReal_compl hE, probReal_univ, hDmass] at hshort
  have hx : ν.real (S i) ∈ Set.Icc (0 : ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hx' : 1 - ν.real (S i) ∈ Set.Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hx.2, by linarith only [hx.1]⟩
  apply kstCoverTransform_le_of_polynomial _ (1 - ν.real (S i)) _
    ⟨measureReal_nonneg, measureReal_le_one⟩ hx'
  · have hp : ν.real (S i) ^ (2000 : ℕ) ≤ 1 - μ.real
        (horizontalRectangle (-64*(k : ℤ),-512*(k : ℤ)) (128*k) (1024*k)) := by
      linarith only [hprod, hshort]
    simpa only [sub_sub_cancel] using hp
  · rw [hBmass] at hi
    simpa only [Fintype.card_fin, sub_sub_cancel] using hi

end
end PottsContinuity.BD12
