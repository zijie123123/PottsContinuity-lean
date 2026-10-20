module

public import PottsContinuity.PlanarTopology.SampledStarActualPorts
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial
noncomputable section

/-- Closing every genuine incident sampled bond supplies at least one bond
on each axis at every retained vertex of a positive-width/height rectangle,
including all four corners. -/
theorem rectangle_closed_star_has_both_axes
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (A : Configuration (rectangleGraph a w h)) (z : RectangleVertex a w h)
    (hclosed : ∀ b : RectanglePrimalBond a w h,
      b.val.source = z.val ∨ b.val.target = z.val → rectanglePrimalBondToEdge a w h b ∉ A) :
    (rectangleSampledBondClosed a w h A ⟨z.val,.horizontal⟩ ∨
      rectangleSampledBondClosed a w h A ⟨(z.val.1-1,z.val.2),.horizontal⟩) ∧
    (rectangleSampledBondClosed a w h A ⟨z.val,.vertical⟩ ∨
      rectangleSampledBondClosed a w h A ⟨(z.val.1,z.val.2-1),.vertical⟩) := by
  have hz := (mem_latticeRectangle a z.val w h).mp z.property
  have hbond (b : LatticeBond)
      (hmem : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h)
      (hincident : b.source = z.val ∨ b.target = z.val) :
      rectangleSampledBondClosed a w h A b :=
    ⟨⟨b,hmem⟩,rfl,hclosed ⟨b,hmem⟩ hincident⟩
  constructor
  · by_cases hx : z.val.1 < a.1+(w : ℤ)
    · left
      apply hbond ⟨z.val,.horizontal⟩ ⟨z.property,?_⟩ (Or.inl rfl)
      rw [mem_latticeRectangle]
      change (a.1 ≤ z.val.1+1 ∧ z.val.1+1 ≤ a.1+w) ∧
        (a.2 ≤ z.val.2 ∧ z.val.2 ≤ a.2+h)
      omega
    · right
      apply hbond _ ?_ (Or.inr ?_)
      · constructor <;> rw [mem_latticeRectangle]
        · change (a.1 ≤ z.val.1-1 ∧ z.val.1-1 ≤ a.1+w) ∧
            (a.2 ≤ z.val.2 ∧ z.val.2 ≤ a.2+h)
          omega
        · change (a.1 ≤ z.val.1-1+1 ∧ z.val.1-1+1 ≤ a.1+w) ∧
            (a.2 ≤ z.val.2 ∧ z.val.2 ≤ a.2+h)
          omega
      · change (z.val.1-1+1,z.val.2) = z.val
        ext <;> simp
  · by_cases hy : z.val.2 < a.2+(h : ℤ)
    · left
      apply hbond ⟨z.val,.vertical⟩ ⟨z.property,?_⟩ (Or.inl rfl)
      rw [mem_latticeRectangle]
      change (a.1 ≤ z.val.1 ∧ z.val.1 ≤ a.1+w) ∧
        (a.2 ≤ z.val.2+1 ∧ z.val.2+1 ≤ a.2+h)
      omega
    · right
      apply hbond _ ?_ (Or.inr ?_)
      · constructor <;> rw [mem_latticeRectangle]
        · change (a.1 ≤ z.val.1 ∧ z.val.1 ≤ a.1+w) ∧
            (a.2 ≤ z.val.2-1 ∧ z.val.2-1 ≤ a.2+h)
          omega
        · change (a.1 ≤ z.val.1 ∧ z.val.1 ≤ a.1+w) ∧
            (a.2 ≤ z.val.2-1+1 ∧ z.val.2-1+1 ≤ a.2+h)
          omega
      · change (z.val.1,z.val.2-1+1) = z.val
        ext <;> simp

/-- All actual face ports of the sampled closed star are connected, including
at boundary vertices and corners. No isolated exterior corner face is added. -/
theorem rectangle_closed_boundary_star_ports_connected
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (A : Configuration (rectangleGraph a w h)) (z : RectangleVertex a w h)
    (hclosed : ∀ b : RectanglePrimalBond a w h,
      b.val.source = z.val ∨ b.val.target = z.val → rectanglePrimalBondToEdge a w h b ∉ A)
    (f g : LatticeVertex)
    (hf : fourCyclePort (rectangleSampledClosedDualGraph a w h A)
      (z.val.1-1,z.val.2-1) (z.val.1,z.val.2-1) z.val (z.val.1-1,z.val.2) f)
    (hg : fourCyclePort (rectangleSampledClosedDualGraph a w h A)
      (z.val.1-1,z.val.2-1) (z.val.1,z.val.2-1) z.val (z.val.1-1,z.val.2) g) :
    (rectangleSampledClosedDualGraph a w h A).Reachable f g := by
  obtain ⟨hHorizontal,hVertical⟩ := rectangle_closed_star_has_both_axes a w h hw hh A z hclosed
  exact rectangle_sampled_star_actual_ports_connected a w h A z.val hHorizontal hVertical f g hf hg

/-- The complete sampled split-star operation, with genuine boundary ports,
separates the original primal marks in the same modified configuration. -/
theorem rectangle_disconnected_of_closed_boundary_star_and_dual_arms
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (A : Configuration (rectangleGraph a w h))
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (z : RectangleVertex a w h)
    (hclosed : ∀ b : RectanglePrimalBond a w h,
      b.val.source = z.val ∨ b.val.target = z.val → rectanglePrimalBondToEdge a w h b ∉ A)
    (s f g t : LatticeVertex)
    (hf : fourCyclePort (rectangleSampledClosedDualGraph a w h A)
      (z.val.1-1,z.val.2-1) (z.val.1,z.val.2-1) z.val (z.val.1-1,z.val.2) f)
    (hg : fourCyclePort (rectangleSampledClosedDualGraph a w h A)
      (z.val.1-1,z.val.2-1) (z.val.1,z.val.2-1) z.val (z.val.1-1,z.val.2) g)
    (hs : s ∈ rectangleLowerDualArc a w h u.val v.val)
    (ht : t ∈ rectangleUpperDualArc a w h u.val v.val)
    (minus : (rectangleSampledClosedDualGraph a w h A).Walk s f)
    (plus : (rectangleSampledClosedDualGraph a w h A).Walk g t) :
    ¬ ActualConnected (rectangleGraph a w h) A u v := by
  obtain ⟨center⟩ := rectangle_closed_boundary_star_ports_connected a w h hw hh A z hclosed f g hf hg
  exact rectangle_disconnected_of_sampled_dual_arms_and_connector a w h A u v hu hv
    s f g t hs ht minus center plus

end
end PottsContinuity.PlanarTopology
