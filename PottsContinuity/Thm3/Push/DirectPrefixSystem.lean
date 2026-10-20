module

public import PottsContinuity.Thm3.Push.CompleteSourceStripLimit
public import PottsContinuity.Thm3.Push.AllHeightTipRecordSelector
public import PottsContinuity.Thm3.RSW.StripEventLimit
public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import PottsContinuity.BD12.TwoBlockConnectivity
public import PottsContinuity.Thm3.RSW.EmbeddedConfinedWalkLift
public import PottsContinuity.Thm3.RSW.StripBandArm
public import PottsContinuity.Thm3.Push.RoundedSourceArmExceptionalScale

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance directPrefixSystemEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- A direct physical prefix exploration. The fields are deterministic
search, actual sampled paths and selected-value locality, with no FK law
or probability estimate included. -/
structure CaseTwoDirectPrefixSystem (n s : ℕ) (hfit : 9*s ≤ 2*n) where
  selectPrefix : CaseTwoTipEndpointRecord n s →
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
    Option (List (RectangleVertex (0,0) (2*n) (2*n)))
  locality : ∀ C D b trace,
    caseTwoTipEndpointSelector n s hfit C = some b → 0 < b.2.val.2 →
    selectPrefix b C = some trace →
    D ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
      C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → selectPrefix b D = some trace
  search : ∀ C b,
    caseTwoConfinedPrefixConfiguration n s hfit b C ∈
      arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b)
        (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
        {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} → (selectPrefix b C).isSome
  paths : ∀ C b trace,
    caseTwoTipEndpointSelector n s hfit C = some b →
    selectPrefix b C = some trace → Nonempty (CaseTwoDirectPrefixSourcePaths n s hfit C b trace)

/-- The direct-prefix interface at the exact source ceiling scale. -/
abbrev RoundedDirectPrefixSystem (n : ℕ) (hn : 13 ≤ n) :=
  CaseTwoDirectPrefixSystem n ((n+8)/9)
    ((rounded_source_both_rectangles_fit n (by omega) (by omega)).1)

end
end PottsContinuity.Push
