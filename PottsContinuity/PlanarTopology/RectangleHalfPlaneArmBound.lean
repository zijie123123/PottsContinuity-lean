module

public import PottsContinuity.PlanarTopology.RectangleConnectionEvents
public import PottsContinuity.PlanarTopology.RectangleHalfPlaneArms
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- Vertical translation preserves every original open half-plane edge. -/
def halfPlaneVerticalOpenTranslationHom (k : ℤ) (ω : LatticeConfiguration) :
    (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1} →g
      (PD.rcInfiniteOpenGraph (edgeTranslate (0,k) ω)).induce {z : LatticeVertex | 0 ≤ z.1} where
  toFun u := ⟨(u.val.1,u.val.2+k),u.property⟩
  map_rel' := by
    intro u v huv
    have hh := (openGraphTranslationIso (0,k) ω).map_rel_iff'.mpr huv
    change (PD.rcInfiniteOpenGraph (edgeTranslate (0,k) ω)).Adj
      (u.val.1+0,u.val.2+k) (v.val.1+0,v.val.2+k) at hh
    change (PD.rcInfiniteOpenGraph (edgeTranslate (0,k) ω)).Adj
      (u.val.1,u.val.2+k) (v.val.1,v.val.2+k)
    simpa only [add_zero] using hh

/-- A far-target rectangle connection from a seed near Left is an actual
half-plane arm after vertical recentering. The target premise is purely geometric. -/
theorem rectangleConnectionEvent_subset_translated_halfPlaneArm
    (W H M s N : ℕ) (ax ay : ℤ) (hax : ax ≤ (M:ℤ)) (T : Set LatticeVertex)
    (hT : ∀ z ∈ T, (z.1,z.2-ay) ∉ latticeBox (0,0) N) :
    rectangleConnectionEvent (0,0) W H (latticeRectangle (ax,ay) s s : Set LatticeVertex) T ⊆
      edgeTranslate (0,-ay) ⁻¹' sampledGraphArmEvent
        (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
        (halfPlaneRectangleSeeds (M+s) s) {v | v.val ∈ latticeBox (0,0) N} := by
  intro ω hω
  obtain ⟨u,hu,v,hv,hconn⟩ := (rectangleConnectionEvent_iff _ _ _ _ _ ω).mp hω
  let f := (halfPlaneVerticalOpenTranslationHom (-ay) ω).comp (rectangleToHalfPlaneOpenHom ω W H)
  refine ⟨f u,?_,f v,?_,hconn.map f⟩
  · apply (mem_halfPlaneRectangleSeeds (M+s) s (f u)).mpr
    have hs := (mem_latticeRectangle (ax,ay) u.val s s).mp hu
    have hd := (mem_latticeRectangle (0,0) u.val W H).mp u.property
    apply (mem_latticeRectangle (0,0) (f u).val (M+s) s).mpr
    have hfu : (f u).val = (u.val.1,u.val.2+ -ay) := rfl
    rw [hfu]
    dsimp only [Prod.fst,Prod.snd] at hs hd ⊢
    omega
  · change (v.val.1,v.val.2+ -ay) ∉ latticeBox (0,0) N
    simpa only [sub_eq_add_neg] using hT v.val hv

/-- Translation invariance makes the arm bound independent of the seed's
vertical position and of the containing rectangle dimensions. -/
theorem rectangleConnectionEvent_le_halfPlaneArm (μ : Measure LatticeConfiguration)
    (W H M s N : ℕ) (ax ay : ℤ) (hax : ax ≤ (M:ℤ))
    (hμ : μ.map (edgeTranslate (0,-ay)) = μ) (T : Set LatticeVertex)
    (hT : ∀ z ∈ T, (z.1,z.2-ay) ∉ latticeBox (0,0) N) :
    μ (rectangleConnectionEvent (0,0) W H (latticeRectangle (ax,ay) s s : Set LatticeVertex) T) ≤
      μ (sampledGraphArmEvent
        (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
        (halfPlaneRectangleSeeds (M+s) s) {v | v.val ∈ latticeBox (0,0) N}) := by
  have hbound := measure_mono (μ := μ)
    (rectangleConnectionEvent_subset_translated_halfPlaneArm W H M s N ax ay hax T hT)
  have hG (u v : {z : LatticeVertex // 0 ≤ z.1}) :
      MeasurableSet {ω : LatticeConfiguration |
        ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Adj u v} :=
    measurableSet_open_adj u.val v.val
  rw [← Measure.map_apply (edgeTranslate_measurable _) (sampledGraphArmEvent_measurableSet _ hG _ _),hμ] at hbound
  exact hbound

/-- The same bound for real probabilities of the actual events. -/
theorem rectangleConnectionEvent_real_le_halfPlaneArm (μ : Measure LatticeConfiguration)
    [IsFiniteMeasure μ] (W H M s N : ℕ) (ax ay : ℤ) (hax : ax ≤ (M:ℤ))
    (hμ : μ.map (edgeTranslate (0,-ay)) = μ) (T : Set LatticeVertex)
    (hT : ∀ z ∈ T, (z.1,z.2-ay) ∉ latticeBox (0,0) N) :
    μ.real (rectangleConnectionEvent (0,0) W H (latticeRectangle (ax,ay) s s : Set LatticeVertex) T) ≤
      μ.real (sampledGraphArmEvent
        (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1})
        (halfPlaneRectangleSeeds (M+s) s) {v | v.val ∈ latticeBox (0,0) N}) :=
  ENNReal.toReal_mono (measure_ne_top μ _)
    (rectangleConnectionEvent_le_halfPlaneArm μ W H M s N ax ay hax hμ T hT)

end
end PottsContinuity.PlanarTopology
