module

public import PottsContinuity.Thm3.Push.ConfinedPrefixCrosscutGeometry

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 RSW Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Forget openness without changing any original source walk. -/
def sourceWalkPairUnderlying {V : Type*} (G : SimpleGraph V) (C : Configuration G)
    (Q : SourceWalkPair (openGraph G C)) : SourceWalkPair G where
  firstStart := Q.firstStart
  secondStart := Q.secondStart
  firstEnd := Q.firstEnd
  secondEnd := Q.secondEnd
  first := Q.first.mapLe (openGraph_le G C)
  second := Q.second.mapLe (openGraph_le G C)

end
end PottsContinuity.Push
