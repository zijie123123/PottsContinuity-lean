module

public import PottsContinuity.PlanarTopology.RectangleConnectionTransport
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

theorem latticeTranslate_injective (a : LatticeVertex) : Function.Injective (latticeTranslate a) := by
  intro u v h
  simpa only [latticeTranslate_neg_cancel] using congrArg (latticeTranslate (-a)) h

theorem measure_rectangleConnectionEvent_translate_image (μ : Measure LatticeConfiguration)
    (a c : LatticeVertex) (hμ : μ.map (edgeTranslate a) = μ) (w h : ℕ)
    (S T : Set LatticeVertex) :
    μ (rectangleConnectionEvent (latticeTranslate a c) w h
      (latticeTranslate a '' S) (latticeTranslate a '' T)) =
    μ (rectangleConnectionEvent c w h S T) := by
  rw [measure_rectangleConnectionEvent_translate μ a c hμ,
    Set.preimage_image_eq S (latticeTranslate_injective a),
    Set.preimage_image_eq T (latticeTranslate_injective a)]

theorem rectangleConnectionEvent_bottom_top (a : LatticeVertex) (w h : ℕ) :
    rectangleConnectionEvent a w h {z | z.2 = a.2} {z | z.2 = a.2+(h:ℤ)} =
      verticalRectangle a w h := by
  ext ω
  rw [rectangleConnectionEvent_iff]
  constructor
  · rintro ⟨u,hu,v,hv,hconn⟩
    exact ⟨u,v,hu,hv,hconn⟩
  · rintro ⟨u,v,hu,hv,hconn⟩
    exact ⟨u,hu,v,hv,hconn⟩

end
end PottsContinuity.PlanarTopology
