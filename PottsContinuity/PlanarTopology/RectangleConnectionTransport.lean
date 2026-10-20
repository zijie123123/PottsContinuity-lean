module

public import PottsContinuity.PlanarTopology.RectangleConnectionEvents
public import PottsContinuity.PlanarTopology.RectangleTranspose
public import PottsContinuity.PlanarTopology.RectangleEventTranslation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

theorem rectangleConnectionEvent_transpose_iff (c : LatticeVertex) (w h : ℕ)
    (S T : Set LatticeVertex) (ω : LatticeConfiguration) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso ω ∈
      rectangleConnectionEvent c.swap h w S T ↔
    ω ∈ rectangleConnectionEvent c w h (Prod.swap ⁻¹' S) (Prod.swap ⁻¹' T) := by
  constructor
  · intro hh
    obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hh
    let f := rectangleOpenTransposeHom c.swap h w
      (latticeConfigurationIsoHomeomorph latticeTransposeIso ω)
    have ht := (rectangleConnectionEvent_iff c.swap.swap w h
      (Prod.swap ⁻¹' S) (Prod.swap ⁻¹' T)
      (latticeConfigurationIsoHomeomorph latticeTransposeIso
        (latticeConfigurationIsoHomeomorph latticeTransposeIso ω))).mpr
      ⟨f u,by simpa [f,rectangleOpenTransposeHom] using hu,
        f v,by simpa [f,rectangleOpenTransposeHom] using hv,hconn.map f⟩
    simpa only [Prod.swap_swap,transposeConfiguration_twice] using ht
  · intro hh
    obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hh
    let f := rectangleOpenTransposeHom c w h ω
    exact (rectangleConnectionEvent_iff _ _ _ _ _ _).mpr ⟨f u,hu,f v,hv,hconn.map f⟩

theorem rectangleConnectionEvent_transpose_preimage (c : LatticeVertex) (w h : ℕ)
    (S T : Set LatticeVertex) :
    latticeConfigurationIsoHomeomorph latticeTransposeIso ⁻¹'
      rectangleConnectionEvent c.swap h w S T =
    rectangleConnectionEvent c w h (Prod.swap ⁻¹' S) (Prod.swap ⁻¹' T) := by
  ext ω
  exact rectangleConnectionEvent_transpose_iff c w h S T ω

theorem transposeLaw_rectangleConnectionEvent (μ : Measure LatticeConfiguration)
    (c : LatticeVertex) (w h : ℕ) (S T : Set LatticeVertex) :
    μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)
      (rectangleConnectionEvent c.swap h w S T) =
    μ (rectangleConnectionEvent c w h (Prod.swap ⁻¹' S) (Prod.swap ⁻¹' T)) := by
  rw [Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable _)
    (rectangleConnectionEvent_measurableSet _ _ _ _ _),rectangleConnectionEvent_transpose_preimage]

theorem rectangleConnectionEvent_translate_iff (a c : LatticeVertex) (w h : ℕ)
    (S T : Set LatticeVertex) (ω : LatticeConfiguration) :
    edgeTranslate a ω ∈ rectangleConnectionEvent (latticeTranslate a c) w h S T ↔
    ω ∈ rectangleConnectionEvent c w h
      (latticeTranslate a ⁻¹' S) (latticeTranslate a ⁻¹' T) := by
  constructor
  · intro hh
    obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hh
    let f := rectangleOpenTranslationHom (-a) (latticeTranslate a c) w h (edgeTranslate a ω)
    have ht := (rectangleConnectionEvent_iff _ _ _
      (latticeTranslate a ⁻¹' S) (latticeTranslate a ⁻¹' T) _).mpr
      ⟨f u,by
        change latticeTranslate a (latticeTranslate (-a) u.val) ∈ S
        simpa [latticeTranslate] using hu,
        f v,by
        change latticeTranslate a (latticeTranslate (-a) v.val) ∈ T
        simpa [latticeTranslate] using hv,hconn.map f⟩
    simpa only [← edgeTranslate_add,neg_add_cancel,edgeTranslate_zero,latticeTranslate_neg_cancel] using ht
  · intro hh
    obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ _).mp hh
    let f := rectangleOpenTranslationHom a c w h ω
    exact (rectangleConnectionEvent_iff _ _ _ _ _ _).mpr ⟨f u,hu,f v,hv,hconn.map f⟩

theorem measure_rectangleConnectionEvent_translate (μ : Measure LatticeConfiguration)
    (a c : LatticeVertex) (hμ : μ.map (edgeTranslate a) = μ) (w h : ℕ)
    (S T : Set LatticeVertex) :
    μ (rectangleConnectionEvent (latticeTranslate a c) w h S T) =
    μ (rectangleConnectionEvent c w h
      (latticeTranslate a ⁻¹' S) (latticeTranslate a ⁻¹' T)) := by
  calc
    _ = μ.map (edgeTranslate a) (rectangleConnectionEvent (latticeTranslate a c) w h S T) := by rw [hμ]
    _ = _ := by
      rw [Measure.map_apply (edgeTranslate_measurable _) (rectangleConnectionEvent_measurableSet _ _ _ _ _)]
      congr 1
      ext ω
      exact rectangleConnectionEvent_translate_iff a c w h S T ω

end
end PottsContinuity.PlanarTopology
