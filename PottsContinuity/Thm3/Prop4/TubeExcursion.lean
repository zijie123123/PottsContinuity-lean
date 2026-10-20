module

public import PottsContinuity.Thm3.Prop4.TubePartition
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Farthest-vertex decomposition of a genuine tube excursion

This is the deterministic content of equation (27), valid for any finite path
trace; the trace is a parameter here and need not be the lowest open path. The
events are used with traces of recorded open paths in
`Thm3.Prop4.RecordedExcursionConvolution`.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- A finite trace has a vertex above the actual Euclidean tube. -/
def tubeExcursionEvent {Ω : Type*} (n : ℕ) (ε : ℝ) (u v : ℤ × ℤ)
    (trace : Ω → Finset (ℤ × ℤ)) : Set Ω :=
  {ω | ∃ z ∈ inductionTubeAbove n ε u v, z ∈ trace ω}

/-- The specified trace vertex maximizes distance among its above-tube vertices. -/
def maximalTubeExcursionEvent {Ω : Type*} (n : ℕ) (ε : ℝ) (u v : ℤ × ℤ)
    (trace : Ω → Finset (ℤ × ℤ)) (z : ℤ × ℤ) : Set Ω :=
  {ω | z ∈ inductionTubeAbove n ε u v ∧ z ∈ trace ω ∧
    ∀ w ∈ inductionTubeAbove n ε u v, w ∈ trace ω → tubeDistance u v w ≤ tubeDistance u v z}

/-- Every excursion has a farthest actual vertex; no nonunique choice is used in a definition. -/
theorem tubeExcursion_eq_union_maximal {Ω : Type*} (n : ℕ) (ε : ℝ)
    (u v : ℤ × ℤ) (trace : Ω → Finset (ℤ × ℤ)) :
    tubeExcursionEvent n ε u v trace =
      ⋃ z ∈ inductionTubeAbove n ε u v, maximalTubeExcursionEvent n ε u v trace z := by
  classical
  ext ω
  constructor
  · rintro ⟨z,hz,htrace⟩
    let S := (inductionTubeAbove n ε u v).filter (fun w => w ∈ trace ω)
    have hS : S.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hz,htrace⟩⟩
    obtain ⟨w,hw,hmax⟩ := Finset.exists_max_image S (tubeDistance u v) hS
    have hw' := Finset.mem_filter.mp hw
    refine Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hw'.1,hw'.1,hw'.2,?_⟩⟩
    intro x hx htx
    exact hmax x (Finset.mem_filter.mpr ⟨hx,htx⟩)
  · intro hω
    obtain ⟨z,hz,hmax⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨z,hz,hmax.2.1⟩

/-- There are at most nine n² candidates at positive scale. -/
theorem inductionTubeAbove_card_le {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (u v : ℤ × ℤ) :
    (inductionTubeAbove n ε u v).card ≤ 9*n^2 := by
  have hIcc : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  have hbox : (box n).card = (2*n+1)^2 := by
    simp only [box,Finset.card_product,hIcc,pow_two]
  have hsmall : (2*n+1)^2 ≤ 9*n^2 := by nlinarith only [hn]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (hbox.le.trans hsmall)

end PottsContinuity.Thm3.Prop4
