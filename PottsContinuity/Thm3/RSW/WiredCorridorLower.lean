module

public import PottsContinuity.Thm3.RSW.WiredRectangleSample
public import PottsContinuity.Thm3.RSW.WiredBoxSwap

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

/-- Exchanging coordinates preserves containment in the centered wired box. -/
theorem rectangle_swap_contained_in_box (a : LatticeVertex) (w h N : ℕ)
    (hbox : PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N) :
    PD.FK.latticeRectangle (a.2,a.1) h w ⊆ latticeBox (0,0) N := by
  intro z hz
  have hz' := (mem_latticeRectangle (a.2,a.1) z h w).mp hz
  have hswap : (z.2,z.1) ∈ PD.FK.latticeRectangle a w h :=
    (mem_latticeRectangle a (z.2,z.1) w h).mpr ⟨hz'.2,hz'.1⟩
  have hb := (mem_latticeBox (0,0) (z.2,z.1) N).mp (hbox hswap)
  exact (mem_latticeBox (0,0) z N).mpr ⟨hb.2,hb.1⟩

/-- One positive coefficient gives both orientations in every actual finite
wired box, for all translated contained rectangles of the stated aspect. -/
theorem selfDual_finite_wired_corridor_lower (q : Set.Ici (1:ℝ))
    (α : ℝ) (hα : 1 < α) :
    ∃ c : ℝ, 0 < c ∧
      (∀ (a : LatticeVertex) (w h N : ℕ),
        0 < w → (w:ℝ) < α*h → PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N →
        c ≤ finiteBoundaryEventProbability (box N) (selfDualParameters q)
          (frozenBoundaryCondition (box N) 1)
          (horizontalCrossing (box N) a.1 (a.1+w) a.2 (a.2+h))) ∧
      (∀ (a : LatticeVertex) (w h N : ℕ),
        0 < h → (h:ℝ) < α*w → PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N →
        c ≤ finiteBoundaryEventProbability (box N) (selfDualParameters q)
          (frozenBoundaryCondition (box N) 1)
          (finiteVerticalCrossing (box N) a.1 (a.1+w) a.2 (a.2+h))) := by
  obtain ⟨c,hc,hbound⟩ := selfDual_finite_wired_horizontal_lower q α hα
  have hH (a : LatticeVertex) (w h N : ℕ) (hw : 0 < w) (hwh : (w:ℝ) < α*h)
      (hbox : PD.FK.latticeRectangle a w h ⊆ latticeBox (0,0) N) :
      c ≤ finiteBoundaryEventProbability (box N) (selfDualParameters q)
        (frozenBoundaryCondition (box N) 1)
        (horizontalCrossing (box N) a.1 (a.1+w) a.2 (a.2+h)) := by
    have hb : latticeBox (0,0) N = PottsContinuity.box N := by
      ext z
      simp only [latticeBox,PottsContinuity.box,
        Finset.mem_product,Finset.mem_Icc,zero_sub,zero_add]
    have h := hbound a w h N hw hwh hbox
    rw [hb] at h
    exact h
  refine ⟨c,hc,hH,?_⟩
  intro a w h N hh hhw hbox
  have hp := hH (a.2,a.1) h w N hh hhw (rectangle_swap_contained_in_box a w h N hbox)
  rw [finite_wired_box_probability_swap (selfDualParameters q) N
    (finiteVerticalCrossing (box N) a.1 (a.1+w) a.2 (a.2+h))]
  apply hp.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro A hA
  exact horizontalCrossing_box_swap N a.2 (a.2+h) a.1 (a.1+w)
    ((boolConfigurationEquiv _).symm A) hA

end
end PottsContinuity.RSW
