module

public import PottsContinuity.Infinite.FiniteGraphComparison
public import PottsContinuity.Thm4Plane.PlaneTranslation

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm4Plane

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK

/-- A finite free FK event on any embedded finite lattice graph is bounded by
the free infinite-volume probability of a translated box-boundary event,
provided the literal whole-plane event induced by the finite graph is included
in that connection event. -/
theorem finite_free_embedded_event_le_centered_box_boundary_probability_of_event_inclusion
    {V : Type*} [Finite V]
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (G : SimpleGraph V) (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (A : Set (Configuration G)) (hA : IsUpperSet A)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q 0 μ)
    (a : LatticeVertex) (n : ℕ)
    (hinclude : Infinite.latticeGraphEvent G f hG A ⊆
      translatedBoxBoundaryConnectionEvent a n) :
    (measure G (Infinite.pdParameters p q hp0 hp1 hq)
      (BoundaryCondition.free ∅) A).toReal ≤
      μ.real (centeredBoxBoundaryConnectionEvent n) := by
  have hfinite := Infinite.finite_graph_free_le_infinite_local
    p q hp0 hp1 hq G f hG A hA μ hμ
  have htranslated : μ (translatedBoxBoundaryConnectionEvent a n) ≤ 1 := by
    calc
      μ (translatedBoxBoundaryConnectionEvent a n) ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := hμ.1.measure_univ
  have htranslated_ne_top : μ (translatedBoxBoundaryConnectionEvent a n) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt htranslated ENNReal.one_lt_top)
  have hcompare :
      μ.real (Infinite.latticeGraphEvent G f hG A) ≤
        μ.real (translatedBoxBoundaryConnectionEvent a n) := by
    change ENNReal.toReal (μ (Infinite.latticeGraphEvent G f hG A)) ≤
      ENNReal.toReal (μ (translatedBoxBoundaryConnectionEvent a n))
    exact ENNReal.toReal_mono htranslated_ne_top (measure_mono hinclude)
  calc
    _ ≤ μ.real (Infinite.latticeGraphEvent G f hG A) := hfinite
    _ ≤ μ.real (translatedBoxBoundaryConnectionEvent a n) := hcompare
    _ = μ.real (centeredBoxBoundaryConnectionEvent n) :=
      translatedBoxBoundaryConnection_probability_eq
        p q hq μ hμ a n

end PottsContinuity.Thm4Plane
