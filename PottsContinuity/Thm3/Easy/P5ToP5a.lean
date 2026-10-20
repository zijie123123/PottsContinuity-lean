module

public import PottsContinuity.Thm3.Easy.P5ToP5aConditional
public import PottsContinuity.Thm3.RSW.PolygonRayAnyLength

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity
open PottsContinuity.PD.FK

/-- P5 gives the corrected uniform annulus circuit bound by the proved
polygon point-location theorem. The annulus scales start at two. -/
theorem p5_implies_p5a
    (q : Set.Ici (1 : ℝ))
    (hP5 : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ rcEventProb
        (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
          (-(n : ℤ)) (2 * (n : ℤ)))
        (criticalParameters q).toP (criticalParameters q).toQ 0
        (horizontalCrossing
          (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
            (-(n : ℤ)) (2 * (n : ℤ)))
          0 ⌊α * (n : ℝ)⌋ 0 n)) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ n : ℕ, 2 ≤ n →
      c₂ ≤ p5aAnnulusProbability (criticalParameters q) n := by
  apply p5_implies_p5a_of_rayIndexPolygonLocation q hP5
  intro z p k P hlength hp hvertices hindex hnot
  exact PottsContinuity.RSW.latticePolygon_mem_domain_of_nonzero_rayIndex
    p P hlength hp hvertices ((0 : ℤ), (0 : ℤ)) hindex hnot

end PottsContinuity.Thm3.Easy
