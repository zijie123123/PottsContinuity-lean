module

public import PottsContinuity.BD12.RectangleConfinedWalk
public import PottsContinuity.BD12.KSTHypotheses

/-! Literal translation of actual confined rectangle crossings and their
wired infinite-volume probabilities. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section

/-- Translated rectangle vertices are exactly the translates of the original vertices. -/
theorem mem_latticeRectangle_translate (b a v : LatticeVertex) (w h : ℕ) :
    latticeTranslate b v ∈ PD.FK.latticeRectangle (latticeTranslate b a) w h ↔
      v ∈ PD.FK.latticeRectangle a w h := by
  rw [mem_latticeRectangle,mem_latticeRectangle]
  dsimp only [latticeTranslate]
  omega

/-- Translation carries a confined actual crossing to the translated rectangle. -/
theorem horizontalRectangle_translate_mem (b a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (hω : ω ∈ horizontalRectangle a w h) :
    edgeTranslate b ω ∈ horizontalRectangle (latticeTranslate b a) w h := by
  obtain ⟨u,v,p,hu,hv,hall⟩ := (horizontalRectangle_iff_confined_open_walk a w h ω).mp hω
  apply (horizontalRectangle_iff_confined_open_walk _ w h _).mpr
  refine ⟨latticeTranslate b u,latticeTranslate b v,p.map (openGraphTranslationIso b ω).toHom,?_,?_,?_⟩
  · change u.1+b.1 = a.1+b.1
    omega
  · change v.1+b.1 = a.1+b.1+(w : ℤ)
    omega
  · intro z hz
    have hs := SimpleGraph.Walk.support_map (openGraphTranslationIso b ω).toHom p
    have hz' : z ∈ p.support.map (openGraphTranslationIso b ω).toHom := hs ▸ hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz'
    exact (mem_latticeRectangle_translate b a x w h).mpr (hall x hx)

/-- Exact two-sided translation identity for actual crossing events. -/
theorem horizontalRectangle_translation (b a : LatticeVertex) (w h : ℕ) (ω : LatticeConfiguration) :
    edgeTranslate b ω ∈ horizontalRectangle (latticeTranslate b a) w h ↔ ω ∈ horizontalRectangle a w h := by
  constructor
  · intro hω
    have h' := horizontalRectangle_translate_mem (-b) (latticeTranslate b a) w h (edgeTranslate b ω) hω
    have hneg : edgeTranslate (-b) (edgeTranslate b ω) = ω := by
      rw [← edgeTranslate_add,neg_add_cancel,edgeTranslate_zero]
    simpa only [hneg,latticeTranslate_neg_cancel] using h'
  · exact horizontalRectangle_translate_mem b a w h ω

/-- Translation preserves actual wired rectangle crossing probabilities. -/
theorem wired_horizontalRectangle_probability_translation (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (b a : LatticeVertex) (w h : ℕ) :
    μ.real (horizontalRectangle (latticeTranslate b a) w h) = μ.real (horizontalRectangle a w h) := by
  have hevent : latticeConfigurationTranslate b ⁻¹' horizontalRectangle (latticeTranslate b a) w h =
      horizontalRectangle a w h := Set.ext (horizontalRectangle_translation b a w h)
  have h' := congrArg (fun ν : Measure LatticeConfiguration => ν (horizontalRectangle (latticeTranslate b a) w h))
    (wired_translation_invariant θ μ hμ b)
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable b)
    (horizontalRectangle_isCylinder _ _ _).measurableSet,hevent] at h'
  exact congrArg ENNReal.toReal h'.symm

/-- Every base point has the same wired crossing probability as the origin. -/
theorem wired_horizontalRectangle_probability_eq_origin (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (a : LatticeVertex) (w h : ℕ) :
    μ.real (horizontalRectangle a w h) = μ.real (horizontalRectangle (0,0) w h) := by
  have ha : latticeTranslate a (0,0) = a := by ext <;> simp [latticeTranslate]
  simpa only [ha] using wired_horizontalRectangle_probability_translation θ μ hμ a (0,0) w h

end
end PottsContinuity.BD12
