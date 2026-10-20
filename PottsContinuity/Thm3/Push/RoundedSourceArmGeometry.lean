module

public import PottsContinuity.Thm3.RSW.StripRoundedGluing

@[expose] public section

namespace PottsContinuity.Push

/-- Both original rectangles R and (2s,0)+R fit inside the source square
at every rounded scale n at least eleven. -/
theorem rounded_source_translated_rectangles_fit (n : ℕ) (hn : 11 ≤ n) :
    11*((n+8)/9) ≤ 2*n := by
  omega

end PottsContinuity.Push
