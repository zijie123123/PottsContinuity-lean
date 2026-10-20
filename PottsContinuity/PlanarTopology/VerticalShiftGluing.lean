module

public import PottsContinuity.PlanarTopology.RectangleGluingProbability
public import PottsContinuity.PlanarTopology.RectangleConnectionImages
public import PottsContinuity.PlanarTopology.BalancedSeedDominantBound

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- Quantitative shifted-Top construction. Both boundary paths retain their
sampled edges; a fixed finite witness supplies the interior connector. -/
theorem vertical_shift_gluing_probability_lower
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (W H s d : ℕ) (v y : Fin (W+1) × Fin (H+1))
    (C : Set LatticeVertex) (S T : Finset LatticeVertex)
    (hCY : C ⊆ (PD.FK.latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex))
    (hVS : (PD.FK.latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) ⊆ S)
    (hYS : (PD.FK.latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex) ⊆ S)
    (hshiftS : latticeTranslate (0,(d:ℤ)) ''
      (PD.FK.latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex) ⊆ S)
    (hTR : (T : Set LatticeVertex) ⊆ PD.FK.latticeRectangle (0,0) (W+s) (H+s))
    (hinterior : ∀ z ∈ T, 0 < z.2 ∧ z.2 < ((H+s:ℕ):ℤ))
    (hcompare : rectangleSeedBottomProbability μ W H s y ≤ rectangleSeedTopProbability μ W H s y) :
    μ.real (infiniteHit C) + 2*rectangleSeedBottomProbability μ W H s v +
      2*μ.real (finiteLocalUniquenessEvent S T) - 4 ≤
        μ.real (verticalRectangle (0,0) (W+s) (H+s+d)) := by
  let V := (PD.FK.latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex)
  let Y := (PD.FK.latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex)
  let a : LatticeVertex := (0,(d:ℤ))
  let L : Set LatticeVertex := {z | z.2 = 0}
  let U : Set LatticeVertex := {z | z.2 = ((H+s:ℕ):ℤ)}
  let U' : Set LatticeVertex := {z | z.2 = ((H+s+d:ℕ):ℤ)}
  have hLT : ∀ z ∈ L, z ∉ T := by
    intro z hz hzT
    have hi := (hinterior z hzT).1
    change z.2 = 0 at hz
    omega
  have hUT : ∀ z ∈ U', z ∉ T := by
    intro z hz hzT
    have hi := (hinterior z hzT).2
    change z.2 = ((H+s+d:ℕ):ℤ) at hz
    omega
  have htransfer := rectangle_connection_transfer_probability_lower μ (0,0) (W+s) (H+s)
    V C L S T hVS (hCY.trans hYS) (hCY.trans (rectangleSeed_subset_rectangle W H s y)) hTR hLT
  have hmono : μ.real (rectangleConnectionEvent (0,0) (W+s) (H+s) C L) ≤
      rectangleSeedBottomProbability μ W H s y := by
    exact measureReal_mono (rectangleConnectionEvent_mono (0,0) (W+s) (H+s) hCY Set.Subset.rfl)
  have hYtop : μ.real (infiniteHit C) + rectangleSeedBottomProbability μ W H s v +
      μ.real (finiteLocalUniquenessEvent S T) - 2 ≤ rectangleSeedTopProbability μ W H s y := by
    change μ.real (infiniteHit C) + rectangleSeedBottomProbability μ W H s v +
      μ.real (finiteLocalUniquenessEvent S T) - 2 ≤ _ at htransfer
    linarith
  have himage : latticeTranslate a '' U = U' := by
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩
      change q.2 = ((H+s:ℕ):ℤ) at hq
      change q.2+(d:ℤ) = ((H+s+d:ℕ):ℤ)
      omega
    · intro hz
      change z.2 = ((H+s+d:ℕ):ℤ) at hz
      refine ⟨(z.1,z.2-(d:ℤ)),?_,?_⟩
      · change z.2-(d:ℤ) = ((H+s:ℕ):ℤ)
        omega
      · ext <;> dsimp [a,latticeTranslate] <;> omega
  have hshift := congrArg ENNReal.toReal (measure_rectangleConnectionEvent_translate_image
    μ a (0,0) (htranslation _) (W+s) (H+s) Y U)
  rw [himage] at hshift
  rw [← Measure.real_def,← Measure.real_def] at hshift
  have ha : latticeTranslate a (0,0) = (0,(d:ℤ)) := by ext <;> simp [a,latticeTranslate]
  rw [ha] at hshift
  change μ.real (rectangleConnectionEvent (0,(d:ℤ)) (W+s) (H+s) (latticeTranslate a '' Y) U') =
    rectangleSeedTopProbability μ W H s y at hshift
  have hD₁ : (PD.FK.latticeRectangle (0,0) (W+s) (H+s) : Set LatticeVertex) ⊆
      PD.FK.latticeRectangle (0,0) (W+s) (H+s+d) := by
    intro z hz
    have hz := (mem_latticeRectangle (0,0) z (W+s) (H+s)).mp hz
    apply (mem_latticeRectangle (0,0) z (W+s) (H+s+d)).mpr
    dsimp at *
    omega
  have hD₂ : (PD.FK.latticeRectangle (0,(d:ℤ)) (W+s) (H+s) : Set LatticeVertex) ⊆
      PD.FK.latticeRectangle (0,0) (W+s) (H+s+d) := by
    intro z hz
    have hz := (mem_latticeRectangle (0,(d:ℤ)) z (W+s) (H+s)).mp hz
    apply (mem_latticeRectangle (0,0) z (W+s) (H+s+d)).mpr
    dsimp at *
    omega
  have hglue := rectangle_connection_glue_probability_lower μ (0,0) (0,0) (0,(d:ℤ))
    (W+s) (H+s+d) (W+s) (H+s) (W+s) (H+s) V (latticeTranslate a '' Y) L U' S T
    hD₁ hD₂ (hTR.trans hD₁) hVS hshiftS hLT hUT
  rw [hshift] at hglue
  have hevent : rectangleConnectionEvent (0,0) (W+s) (H+s+d) L U' =
      verticalRectangle (0,0) (W+s) (H+s+d) := by
    simpa only [Prod.snd_zero,zero_add] using rectangleConnectionEvent_bottom_top (0,0) (W+s) (H+s+d)
  rw [hevent] at hglue
  change rectangleSeedBottomProbability μ W H s v + rectangleSeedTopProbability μ W H s y +
    μ.real (finiteLocalUniquenessEvent S T) - 2 ≤ _ at hglue
  linarith

end
end PottsContinuity.PlanarTopology
