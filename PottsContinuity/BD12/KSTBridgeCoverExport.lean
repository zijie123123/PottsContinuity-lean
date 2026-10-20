module

public import PottsContinuity.BD12.KSTFiniteAssociation
public import PottsContinuity.BD12.KSTHypotheses
public import PottsContinuity.BD12.KSTCoverTransform
public import PottsContinuity.PlanarTopology.KSTBridgeFiniteCover

/-! The finite bridge cover of `PlanarTopology.KSTBridgeFiniteCover`, applied to the actual
wired limit. This proves KST first-relation (i) at the integral scales of that cover. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK
noncomputable section

/-- Every box-preserving isometry preserves actual wired event probabilities. -/
theorem wired_isometry_preimage_real (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (e : PD.squareLattice ≃g PD.squareLattice)
    (he : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r)
    (A : Set LatticeConfiguration) (hA : MeasurableSet A) :
    μ.real (latticeConfigurationIsoHomeomorph e ⁻¹' A) = μ.real A := by
  have hi := Infinite.infinite_volume_latticeIso_invariant θ.toP θ.toQ
    (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property 1 μ hμ e he
  change (μ (latticeConfigurationIsoHomeomorph e ⁻¹' A)).toReal = (μ A).toReal
  rw [← Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable e) hA, hi]

/-- The exact polynomial cover/gluing relation, including probability endpoints.
There is no geometric premise: `PlanarTopology.kst_bridge_finite_cover` supplies the actual
finite cover and gluing. -/
theorem wired_kst_bridge_cover_polynomial (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m : ℕ) (hm : 192 ∣ m) (hmpos : 1 ≤ m) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - x) ^ (2000 : ℕ) ≤ 1 - μ.real (kstBridge m) ∧
      x ^ (2000 : ℕ) ≤ μ.real (horizontalRectangle (-8*(m : ℤ),-(m : ℤ)) (16*m) (2*m)) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨S, hS, hcover, hglue⟩ := PlanarTopology.kst_bridge_finite_cover m hm hmpos
  have hFKG := fun A B => @wired_measurable_positive_association θ μ hμ A B
  obtain ⟨i, hi⟩ := kst_finite_cover_square_root μ hFKG S
    (fun i => (hS i).1.measurableSet) (fun i => (hS i).2) hcover
  obtain ⟨e, he, hglue⟩ := hglue i
  refine ⟨μ.real (S i), ⟨measureReal_nonneg, measureReal_le_one⟩, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using hi
  · have hprod := kst_construction_of_kstCorridor μ hFKG
      (fun j => latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i)
      (fun j => (PlanarTopology.isCylinder_iso_preimage (e j) (hS i).1).measurableSet)
      (fun j => PlanarTopology.isUpperSet_iso_preimage (e j) (hS i).2) hglue
    have hsym (j : Fin 2000) :
        μ.real (latticeConfigurationIsoHomeomorph (e j) ⁻¹' S i) = μ.real (S i) :=
      wired_isometry_preimage_real θ μ hμ (e j) (he j) (S i) (hS i).1.measurableSet
    simpa only [hsym, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

/-- KST first-relation (i), with the literal f_1 and exponent 2000, for all
wired FK parameters and all positive scales divisible by 192. -/
theorem wired_kst_bridge_cover_lower_bound (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m : ℕ) (hm : 192 ∣ m) (hmpos : 1 ≤ m) :
    kstCoverTransform (μ.real (kstBridge m)) ≤
      μ.real (horizontalRectangle (-8*(m : ℤ),-(m : ℤ)) (16*m) (2*m)) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨x, hx, hcover, hglue⟩ := wired_kst_bridge_cover_polynomial θ μ hμ m hm hmpos
  exact kstCoverTransform_le_of_polynomial _ x _ ⟨measureReal_nonneg, measureReal_le_one⟩ hx hcover hglue

end
end PottsContinuity.BD12
