module

public import PottsContinuity.Thm3.Push.EmbeddedArcErasure
public import PottsContinuity.PD.Duality.Rectangle

@[expose] public section

namespace PottsContinuity.Push
open PD.FK

/-- Coordinate-preserving inclusion of a bottom band in a taller rectangle. -/
def rectangleBandEmbedding (a : LatticeVertex) (w b h : ℕ) (hbh : b ≤ h) :
    RectangleVertex a w b ↪ RectangleVertex a w h where
  toFun v := ⟨v.val,by
    have hv := (mem_latticeRectangle a v.val w b).mp v.property
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro u v he
    apply Subtype.ext
    exact congrArg (fun z : RectangleVertex a w h => z.val) he

/-- Every original band edge remains the same sampled bond of the host. -/
theorem rectangleBandEmbedding_map_le (a : LatticeVertex) (w b h : ℕ) (hbh : b ≤ h) :
    (rectangleGraph a w b).map (rectangleBandEmbedding a w b h hbh) ≤ rectangleGraph a w h := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  exact huv

end PottsContinuity.Push
