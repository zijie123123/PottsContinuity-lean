-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/WindingCircle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.Winding

/-!
# The positive orientation of the standard circle

The plane loop is the actual once-counterclockwise complex unit circle.
Its winding about the origin
is proved to be one from the explicit angle lift, fixing the normalization of
our geometric winding number without an assumed orientation convention.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set
open scoped unitInterval

noncomputable section

/-- The actual unit circle traversed once as exp(2*pi*i*t), as a complex loop. -/
def standardCircleLoop : Path (1 : ℂ) 1 where
  toFun t := Circle.exp (2 * Real.pi * t)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] theorem standardCircleLoop_apply (t : I) :
    standardCircleLoop t = (Circle.exp (2 * Real.pi * t) : ℂ) := rfl

end

end PottsContinuity.FKC
