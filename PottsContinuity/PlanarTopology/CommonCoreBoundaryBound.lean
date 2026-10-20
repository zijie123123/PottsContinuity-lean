module

public import PottsContinuity.PlanarTopology.RectangleBoundaryExit
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- A single infinite root in the common core gives one of four actual
boundary connections, allowing a different containing seed for each side. -/
theorem infiniteHit_subset_rectangle_four_seed_union (a : LatticeVertex) (w h : ℕ)
    (C SL SR SB ST : Set LatticeVertex) (hC : C ⊆ latticeRectangle a w h)
    (hL : C ⊆ SL) (hR : C ⊆ SR) (hB : C ⊆ SB) (hT : C ⊆ ST) :
    infiniteHit C ⊆
      rectangleConnectionEvent a w h SL {z | z.1 = a.1} ∪
      rectangleConnectionEvent a w h SR {z | z.1 = a.1+(w:ℤ)} ∪
      rectangleConnectionEvent a w h SB {z | z.2 = a.2} ∪
      rectangleConnectionEvent a w h ST {z | z.2 = a.2+(h:ℤ)} := by
  intro ω hω
  rcases infiniteHit_subset_rectangle_side_union a w h C hC hω with ((hω | hω) | hω) | hω
  · exact Or.inl (Or.inl (Or.inl (rectangleConnectionEvent_mono a w h hL Set.Subset.rfl hω)))
  · exact Or.inl (Or.inl (Or.inr (rectangleConnectionEvent_mono a w h hR Set.Subset.rfl hω)))
  · exact Or.inl (Or.inr (rectangleConnectionEvent_mono a w h hB Set.Subset.rfl hω))
  · exact Or.inr (rectangleConnectionEvent_mono a w h hT Set.Subset.rfl hω)

/-- The four-seed union bound retains the same infinite-root event on the
left. No separate infinite-root witnesses or independence are assumed. -/
theorem infiniteHit_real_le_rectangle_four_seed_sum
    (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    (a : LatticeVertex) (w h : ℕ) (C SL SR SB ST : Set LatticeVertex)
    (hC : C ⊆ latticeRectangle a w h) (hL : C ⊆ SL) (hR : C ⊆ SR) (hB : C ⊆ SB) (hT : C ⊆ ST) :
    μ.real (infiniteHit C) ≤
      μ.real (rectangleConnectionEvent a w h SL {z | z.1 = a.1}) +
      μ.real (rectangleConnectionEvent a w h SR {z | z.1 = a.1+(w:ℤ)}) +
      μ.real (rectangleConnectionEvent a w h SB {z | z.2 = a.2}) +
      μ.real (rectangleConnectionEvent a w h ST {z | z.2 = a.2+(h:ℤ)}) := by
  have hmono := measureReal_mono (μ := μ)
    (infiniteHit_subset_rectangle_four_seed_union a w h C SL SR SB ST hC hL hR hB hT)
  have h₁ := measureReal_union_le (μ := μ)
    (rectangleConnectionEvent a w h SL {z | z.1 = a.1})
    (rectangleConnectionEvent a w h SR {z | z.1 = a.1+(w:ℤ)})
  have h₂ := measureReal_union_le (μ := μ)
    (rectangleConnectionEvent a w h SL {z | z.1 = a.1} ∪
      rectangleConnectionEvent a w h SR {z | z.1 = a.1+(w:ℤ)})
    (rectangleConnectionEvent a w h SB {z | z.2 = a.2})
  have h₃ := measureReal_union_le (μ := μ)
    (rectangleConnectionEvent a w h SL {z | z.1 = a.1} ∪
      rectangleConnectionEvent a w h SR {z | z.1 = a.1+(w:ℤ)} ∪
      rectangleConnectionEvent a w h SB {z | z.2 = a.2})
    (rectangleConnectionEvent a w h ST {z | z.2 = a.2+(h:ℤ)})
  linarith

end
end PottsContinuity.PlanarTopology
