module

public import PottsContinuity.PlanarMixed.FiniteSlit.FirstContactCrop
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

@[expose] public section

namespace PottsContinuity.Push
open PlanarMixed.FiniteSlit

/-- The complete ordered support of the crop depends only on the retained
prefix. In particular, both its vertex trace and every original edge of that
prefix are independent of an appended discarded suffix. -/
theorem retained_support_append_eq_of_le_length
    {V : Type*} {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) (k : ℕ) (hk : k ≤ p.length) :
    ((p.append q).take k).support = (p.take k).support := by
  rw [SimpleGraph.Walk.support_take,SimpleGraph.Walk.support_take,SimpleGraph.Walk.support_append]
  apply List.take_append_of_le_length
  rw [SimpleGraph.Walk.length_support]
  omega

end PottsContinuity.Push
