module

public import PottsContinuity.BD12.WiredAspectTwoAllScales
public import PottsContinuity.PlanarTopology.KSTAspectRatio

/-! Wired crossings at every integer aspect ratio and every even height.
The exact gluing inclusion `PlanarTopology.kst_aspect_ratio_gluing` is consumed by
finite FKG and symmetry. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- Uniform crossing bounds for all integer aspects at even heights. -/
theorem wired_selfDual_even_height_aspect_lower_bound (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ)
    (ρ : ℕ) (hρ : 1 ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ μ.real (horizontalRectangle (-((ρ*n : ℕ) : ℤ),-(n : ℤ)) (2*ρ*n) (2*n)) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨a,ha,hbase⟩ := wired_selfDual_aspect_two_all_scales_lower_bound q μ hμ
  refine ⟨a^(2*ρ-1),pow_pos ha _,fun n hn => ?_⟩
  obtain ⟨e,he,hglue⟩ := PlanarTopology.kst_aspect_ratio_gluing ρ n hρ hn
  let A := horizontalRectangle (-2*(n : ℤ),-(n : ℤ)) (4*n) (2*n)
  have hAlower : a ≤ μ.real A := (hbase (2*n) (4*n) (by omega) (by omega)).trans_eq
    (wired_horizontalRectangle_probability_eq_origin (criticalParameters q) μ hμ _ _ _).symm
  have hsym (j : Fin (2*ρ-1)) : μ.real (latticeConfigurationIsoHomeomorph (e j) ⁻¹' A) = μ.real A :=
    wired_isometry_preimage_real (criticalParameters q) μ hμ (e j) (he j) A
      (horizontalRectangle_isCylinder _ _ _).measurableSet
  have h := kst_construction_uniform_of_kstCorridor μ
    (fun _ _ => wired_measurable_positive_association (criticalParameters q) μ hμ)
    (fun j => latticeConfigurationIsoHomeomorph (e j) ⁻¹' A)
    (fun j => (horizontalRectangle_isCylinder _ _ _).measurableSet.preimage
      (latticeConfigurationIsoHomeomorph_measurable (e j)))
    (fun j => PlanarTopology.isUpperSet_iso_preimage (e j) (horizontalRectangle_isUpperSet _ _ _))
    hglue a ha.le (fun j => (hsym j).symm ▸ hAlower)
  simpa only [Fintype.card_fin] using h

end
end PottsContinuity.BD12
