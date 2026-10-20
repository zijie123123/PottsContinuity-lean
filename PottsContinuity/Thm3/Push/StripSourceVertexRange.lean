module

public import PottsContinuity.Thm3.Push.IntervalArmStripWindowEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PD.FK

/-- The translated source-square image is exactly its coordinate rectangle
inside the strip, including every side and corner vertex. -/
theorem mem_range_intervalArmStripGraphEmbedding_iff (n : ℕ) (x : ℤ)
    (w : RSW.stripVertices n) :
    w ∈ Set.range (intervalArmStripGraphEmbedding n x) ↔
      x ≤ w.val.1 ∧ w.val.1 ≤ x+2*(n:ℤ) ∧ 0 ≤ w.val.2 ∧ w.val.2 ≤ 2*(n:ℤ) := by
  constructor
  · rintro ⟨v,rfl⟩
    have hv := (PD.FK.mem_latticeRectangle (0,0) v.val (2*n) (2*n)).mp v.property
    change x ≤ x+v.val.1 ∧ x+v.val.1 ≤ x+2*(n:ℤ) ∧ 0 ≤ v.val.2 ∧ v.val.2 ≤ 2*(n:ℤ)
    dsimp at hv
    constructor <;> omega
  · intro hw
    let v : RectangleVertex (0,0) (2*n) (2*n) := ⟨(w.val.1-x,w.val.2),by
      apply (PD.FK.mem_latticeRectangle (0,0) _ (2*n) (2*n)).mpr
      dsimp
      constructor <;> constructor <;> omega⟩
    refine ⟨v,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change x+(w.val.1-x)=w.val.1
      omega
    · rfl

end PottsContinuity.Push
