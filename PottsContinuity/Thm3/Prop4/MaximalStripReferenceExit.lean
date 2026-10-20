module

public import PottsContinuity.Thm3.Prop4.MaximalStripCropComparison
public import PottsContinuity.Thm3.Prop4.MaximalStripDeletedEmbedding
public import PottsContinuity.Thm3.Prop4.DeletedReferenceFirstExit

/-!
# A genuine sampled dual exit above the maximal supporting line

The finite touch lower bound passes through the literal crop, its deleted
ambient embedding and the exact true-dual marginal. The first-boundary prefix
removes all extra ambient edges while preserving the upper half-plane path.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The genuine sampled reference has a polynomial root-to-exterior arm above
the tangent. Only touch and deterministic original-reveal containment are inputs. -/
theorem maximal_strip_reference_exit_lower_of_touch (q : Set.Ici (1 : ℝ))
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (R : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (hR : ∀ e ∈ R,
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source ≤ tiltedHeight t z ∧
      tiltedHeight t (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target ≤ tiltedHeight t z)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) ≤
      (measure (edgeRestriction (rectangleDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
          (rectangleCrossedEdges (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) R))
        (RSW.selfDualParameters q) (rectangleDualBoundaryCondition (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
        (pathConfinedTargetEvent _ {w | tiltedHeight t z ≤ tiltedHeight t w.val}
          {w | w.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)} ⟨z,hz⟩)).toReal := by
  let C := maximalStripCrop n (4*n+4) (4*n+4) t z
  let f := maximalStripEmbedding n (4*n+4) (4*n+4) t z
  let G := (squareLattice.induce (tiltedWindow (4*n+4) (4*n+4) t : Set LatticeVertex)).induce C
  let H := edgeRestriction (rectangleDualAmbientGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (rectangleAmbientCrossedReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) R)
  let x : C := ⟨tiltedWindowOrigin (4*n+4) (4*n+4) t,
    tiltedWindowOrigin_mem_maximalStripCrop n (4*n+4) (4*n+4) t z hz⟩
  let W : Set (RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :=
    {w | w.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}
  have hmap : G.map f ≤ H := maximalStripEmbedding_map_le_deleted n (4*n+4) (4*n+4) t z R hR
  have hcompare := embedded_wired_confined_target_probability_le G H f hmap (RSW.selfDualParameters q) W x
  have hpre : f ⁻¹' W = Subtype.val ⁻¹' maximalStripSeparator n (4*n+4) (4*n+4) t z := rfl
  rw [hpre] at hcompare
  have hLower := (maximal_strip_crop_probability_lower_of_touch q n t ht z hz hTouch).trans hcompare
  have hActual := hLower.trans (rectangle_deleted_ambient_confined_exit_probability_le_actual
    (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) R (RSW.selfDualParameters q) (Set.range f) (f x))
  apply hActual.trans (measureReal_mono ?_ (measure_ne_top _ _))
  have hroot : f x = (⟨z,hz⟩ : RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) := by
    apply Subtype.ext
    change latticeTranslate z (0,0) = z
    simp only [latticeTranslate,zero_add]
  rw [hroot]
  rintro A ⟨y,hy,p,hp⟩
  refine ⟨y,hy,p,?_⟩
  intro w hw
  obtain ⟨b,rfl⟩ := hp w hw
  exact maximalStrip_height_ge_root (4*n+4) (4*n+4) t z b.val

end
end PottsContinuity.Thm3.Prop4
