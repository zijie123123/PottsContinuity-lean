module

public import PottsContinuity.Thm3.Push.StripTranslationConfined
public import PottsContinuity.Thm3.Push.StripReflectionConfined
public import PottsContinuity.Thm3.Push.StripSideArmEvent

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- Actual strip reflection about the centre of R' preserves its bottom arc
and swaps its two side targets, including all corners and boundary vertices. -/
theorem strip_limit_case_two_confined_sides_eq (θ : Parameters) (n s : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ) (x : ℤ) :
    μ.real (RSW.stripConfinedConnection n
      (RSW.stripRectangleVertices n (x+4*(s:ℤ)) (x+9*(s:ℤ)) 0 (2*(n:ℤ)))
      {w | w.val ∈ Set.Icc (x+6*(s:ℤ)) (x+7*(s:ℤ)) ×ˢ ({0} : Set ℤ)}
      {w | w.val.1=x+4*(s:ℤ)}) =
    μ.real (RSW.stripConfinedConnection n
      (RSW.stripRectangleVertices n (x+4*(s:ℤ)) (x+9*(s:ℤ)) 0 (2*(n:ℤ)))
      {w | w.val ∈ Set.Icc (x+6*(s:ℤ)) (x+7*(s:ℤ)) ×ˢ ({0} : Set ℤ)}
      {w | w.val.1=x+9*(s:ℤ)}) := by
  let S := RSW.stripRectangleVertices n (x+4*(s:ℤ)) (x+9*(s:ℤ)) 0 (2*(n:ℤ))
  let A : Set (RSW.stripVertices n) :=
    {w | w.val ∈ Set.Icc (x+6*(s:ℤ)) (x+7*(s:ℤ)) ×ˢ ({0} : Set ℤ)}
  let B : Set (RSW.stripVertices n) := {w | w.val.1=x+4*(s:ℤ)}
  let f := (stripHorizontalReflectionIso n).toEquiv
  let g := (stripTranslationIso n (2*x+13*(s:ℤ))).toEquiv
  have hS : (S.map f.toEmbedding).map g.toEmbedding = S := by
    ext w
    rw [Finset.mem_map_equiv,Finset.mem_map_equiv]
    simp only [S,RSW.stripRectangleVertices,Finset.mem_preimage,latticeRectangle,
      Finset.mem_product,Finset.mem_Icc]
    change ((x+4*(s:ℤ) ≤ -(w.val.1-(2*x+13*(s:ℤ))) ∧
      -(w.val.1-(2*x+13*(s:ℤ))) ≤ x+9*(s:ℤ)) ∧
      0 ≤ w.val.2 ∧ w.val.2 ≤ 2*(n:ℤ)) ↔ _
    omega
  have hA : g '' (f '' A) = A := by
    ext w
    rw [Set.mem_image_equiv,Set.mem_image_equiv]
    change (-(w.val.1-(2*x+13*(s:ℤ))),w.val.2) ∈
      Set.Icc (x+6*(s:ℤ)) (x+7*(s:ℤ)) ×ˢ ({0} : Set ℤ) ↔ _
    simp only [A,Set.mem_ofPred_eq,Set.mem_prod,Set.mem_Icc,Set.mem_singleton_iff]
    omega
  have hB : g '' (f '' B) = {w : RSW.stripVertices n | w.val.1=x+9*(s:ℤ)} := by
    ext w
    rw [Set.mem_image_equiv,Set.mem_image_equiv]
    change -(w.val.1-(2*x+13*(s:ℤ)))=x+4*(s:ℤ) ↔ w.val.1=x+9*(s:ℤ)
    omega
  have h₁ := strip_limit_confined_reflection θ n μ hμ S A B
  have h₂ := strip_limit_confined_translation θ n (2*x+13*(s:ℤ)) μ hμ
    (S.map f.toEmbedding) (f '' A) (f '' B)
  change μ.real (RSW.stripConfinedConnection n (S.map f.toEmbedding) (f '' A) (f '' B)) =
    μ.real (RSW.stripConfinedConnection n ((S.map f.toEmbedding).map g.toEmbedding)
      (g '' (f '' A)) (g '' (f '' B))) at h₂
  rw [hS,hA,hB] at h₂
  exact h₁.trans h₂

/-- The two actual source-square side-arm cylinders have equal probability
under the genuine strip law; the ambient arbitrary source boundary is not used. -/
theorem strip_limit_case_two_source_sides_eq (θ : Parameters) (n s : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (x : ℤ) (hscale : 9*s ≤ 2*n) :
    μ.real (stripSourceSquareEvent n x (sourceCaseTwoSecondArm n s)) =
      μ.real (stripSourceSquareEvent n x (sourceSquareSideArmEvent (2*n)
        (6*(s:ℤ)) (7*(s:ℤ)) (4*(s:ℤ)) (9*(s:ℤ)) (9*(s:ℤ)))) := by
  rw [stripSourceSideArmEvent_eq_confined n x (6*(s:ℤ)) (7*(s:ℤ))
    (4*(s:ℤ)) (9*(s:ℤ)) (4*(s:ℤ)) (by omega) (by omega)]
  rw [stripSourceSideArmEvent_eq_confined n x (6*(s:ℤ)) (7*(s:ℤ))
    (4*(s:ℤ)) (9*(s:ℤ)) (9*(s:ℤ)) (by omega) (by omega)]
  exact strip_limit_case_two_confined_sides_eq θ n s μ hμ x

end
end PottsContinuity.Push
