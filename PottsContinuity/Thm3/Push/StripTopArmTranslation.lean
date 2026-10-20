module

public import PottsContinuity.Thm3.Push.StripTopArmEvent
public import PottsContinuity.Thm3.Push.StripTranslationConfined

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- The confined J-to-top arm is exactly the translate of the original
confined I-to-top arm in probability under the genuine strip law. -/
theorem strip_limit_top_arm_eq_translated_second (θ : Parameters) (n s : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (x : ℤ) (hscale : 11*s ≤ 2*n) :
    μ.real (stripSourceSquareEvent n x (sourceSquareTopArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)))) =
    μ.real (stripSourceSquareEvent n x (sourceSquareTopArmEvent (2*n)
      (6*(s:ℤ)) (7*(s:ℤ)) (2*(s:ℤ)) (11*(s:ℤ)))) := by
  rw [stripSourceTopArmEvent_eq_confined n x (4*(s:ℤ)) (5*(s:ℤ))
    0 (9*(s:ℤ)) (by omega) (by omega)]
  rw [stripSourceTopArmEvent_eq_confined n x (6*(s:ℤ)) (7*(s:ℤ))
    (2*(s:ℤ)) (11*(s:ℤ)) (by omega) (by omega)]
  let S := RSW.stripRectangleVertices n x (x+9*(s:ℤ)) 0 (2*(n:ℤ))
  let A : Set (RSW.stripVertices n) :=
    {w | w.val ∈ Set.Icc (x+4*(s:ℤ)) (x+5*(s:ℤ)) ×ˢ ({0} : Set ℤ)}
  let B : Set (RSW.stripVertices n) := {w | w.val.2=2*(n:ℤ)}
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
  have hB : g '' B = {w : RSW.stripVertices n | w.val.2=2*(n:ℤ)} := by
    ext w
    rw [Set.mem_image_equiv]
    rfl
  have h := strip_limit_confined_translation θ n (2*(s:ℤ)) μ hμ S A B
  change μ.real (RSW.stripConfinedConnection n S A B) =
    μ.real (RSW.stripConfinedConnection n (S.map g.toEmbedding) (g '' A) (g '' B)) at h
  rw [hS,hA,hB] at h
  simpa only [add_zero] using h

end
end PottsContinuity.Push
