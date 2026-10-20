module

public import PottsContinuity.Thm3.Push.StripCaseTwoLeftArmBound

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- The wider J-to-right-side arm is exactly the translate of the original
I-to-right-side arm in probability under the genuine strip law. -/
theorem strip_limit_case_two_first_eq_wide_second (θ : Parameters) (n s : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (x : ℤ) (hscale : 11*s ≤ 2*n) :
    μ.real (stripSourceSquareEvent n x (sourceCaseTwoFirstArm n s)) =
    μ.real (stripSourceSquareEvent n x (sourceSquareSideArmEvent (2*n)
      (6*(s:ℤ)) (7*(s:ℤ)) (2*(s:ℤ)) (11*(s:ℤ)) (11*(s:ℤ)))) := by
  rw [stripSourceSideArmEvent_eq_confined n x (4*(s:ℤ)) (5*(s:ℤ))
    0 (9*(s:ℤ)) (9*(s:ℤ)) (by omega) (by omega)]
  rw [stripSourceSideArmEvent_eq_confined n x (6*(s:ℤ)) (7*(s:ℤ))
    (2*(s:ℤ)) (11*(s:ℤ)) (11*(s:ℤ)) (by omega) (by omega)]
  let S := RSW.stripRectangleVertices n x (x+9*(s:ℤ)) 0 (2*(n:ℤ))
  let A : Set (RSW.stripVertices n) :=
    {w | w.val ∈ Set.Icc (x+4*(s:ℤ)) (x+5*(s:ℤ)) ×ˢ ({0} : Set ℤ)}
  let B : Set (RSW.stripVertices n) := {w | w.val.1=x+9*(s:ℤ)}
  let g := (stripTranslationIso n (2*(s:ℤ))).toEquiv
  have hS : S.map g.toEmbedding =
      RSW.stripRectangleVertices n (x+2*(s:ℤ)) (x+11*(s:ℤ)) 0 (2*(n:ℤ)) := by
    ext w
    rw [Finset.mem_map_equiv]
    simp only [S,RSW.stripRectangleVertices,Finset.mem_preimage,latticeRectangle,
      Finset.mem_product,Finset.mem_Icc]
    change ((x ≤ w.val.1-2*(s:ℤ) ∧ w.val.1-2*(s:ℤ) ≤ x+9*(s:ℤ)) ∧
      0 ≤ w.val.2 ∧ w.val.2 ≤ 2*(n:ℤ)) ↔ _
    omega
  have hA : g '' A =
      {w : RSW.stripVertices n | w.val ∈ Set.Icc (x+6*(s:ℤ)) (x+7*(s:ℤ)) ×ˢ ({0} : Set ℤ)} := by
    ext w
    rw [Set.mem_image_equiv]
    change (w.val.1-2*(s:ℤ),w.val.2) ∈
      Set.Icc (x+4*(s:ℤ)) (x+5*(s:ℤ)) ×ˢ ({0} : Set ℤ) ↔ _
    simp only [Set.mem_ofPred_eq,Set.mem_prod,Set.mem_Icc,Set.mem_singleton_iff]
    omega
  have hB : g '' B = {w : RSW.stripVertices n | w.val.1=x+11*(s:ℤ)} := by
    ext w
    rw [Set.mem_image_equiv]
    change w.val.1-2*(s:ℤ)=x+9*(s:ℤ) ↔ w.val.1=x+11*(s:ℤ)
    omega
  have h := strip_limit_confined_translation θ n (2*(s:ℤ)) μ hμ S A B
  change μ.real (RSW.stripConfinedConnection n S A B) =
    μ.real (RSW.stripConfinedConnection n (S.map g.toEmbedding) (g '' A) (g '' B)) at h
  rw [hS,hA,hB] at h
  simpa only [add_zero] using h

/-- The original right arm alone supplies the printed second-arm bound;
translation, narrower-rectangle restriction and reflection are all proved. -/
theorem strip_case_two_second_arm_ge_sixth_of_first (θ : Parameters) (n s : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (x : ℤ) (hscale : 11*s ≤ 2*n) (c₁ : ℝ)
    (hfirst : c₁/3 ≤ μ.real (stripSourceSquareEvent n x (sourceCaseTwoFirstArm n s))) :
    c₁/6 ≤ μ.real (stripSourceSquareEvent n x (sourceCaseTwoSecondArm n s)) := by
  apply strip_case_two_left_arm_ge_sixth θ n s μ hμ x (by omega) c₁
  rwa [← strip_limit_case_two_first_eq_wide_second θ n s μ hμ x hscale]

end
end PottsContinuity.Push
