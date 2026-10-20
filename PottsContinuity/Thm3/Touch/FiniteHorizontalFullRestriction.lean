module

public import PottsContinuity.Thm3.Touch.FiniteHorizontalArcTransport
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity.PD.FK
open PottsContinuity.Thm3.Prop4
open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.PlanarTopology

/-- The coordinate inclusion of the left split carrier into the full strip. -/
def horizontalLeftHalfVertexEmbedding (n L : ℕ) :
    TiltedColumnLeftHalfVertex n L ↪ TiltedColumnVertex n L 0 where
  toFun z := ⟨z.val, (mem_tiltedColumnLeftHalfDomain n L 0 z.val).mp z.property |>.1⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    have hv := congrArg (fun z : TiltedColumnVertex n L 0 => z.val) h
    simpa using hv

end PottsContinuity.Thm3.Touch
