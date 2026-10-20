module

public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutActive
public import PottsContinuity.PlanarMixed.RetainedWalk
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.PlanarMixed.CrosscutOpenWalks
public import PottsContinuity.PD.FK.ConditionalLaw

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12
noncomputable section
local instance finiteSlitSourcePathsEdgeDecidableEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Compose two literal graph inclusions. -/
theorem composed_map_le {V W U : Type*}
    (G : SimpleGraph V) (S : SimpleGraph W) (H : SimpleGraph U)
    (i : V ↪ W) (j : W ↪ U) (hGS : G.map i ≤ S) (hSH : S.map j ≤ H) :
    G.map (i.trans j) ≤ H := by
  intro u v huv
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact hSH ((SimpleGraph.map_adj _ _ _ _).mpr
    ⟨i a,i b,hGS ((SimpleGraph.map_adj _ _ _ _).mpr ⟨a,b,hab,rfl,rfl⟩),rfl,rfl⟩)

/-- Removing exposed edges preserves an embedded graph inclusion. -/
theorem active_map_le {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U)
    (R : Configuration G) (f : V ↪ U) (h : G.map f ≤ H) :
    (edgeRestriction G R).map f ≤ H := by
  intro u v huv
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact h ((SimpleGraph.map_adj _ _ _ _).mpr ⟨a,b,edgeRestriction_le G R hab,rfl,rfl⟩)

end
end PottsContinuity.PlanarMixed.FiniteSlit
