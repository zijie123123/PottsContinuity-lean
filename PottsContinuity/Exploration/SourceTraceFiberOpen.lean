module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourceExteriorReveals
public import PottsContinuity.PlanarMixed.CutExteriorReveals
public import PottsContinuity.PlanarMixed.FiniteSlit.NativeSourceArms
public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleSourceArms

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK
open PottsContinuity.PlanarMixed
open PottsContinuity.PlanarMixed.FiniteSlit

noncomputable section

local instance sourceTraceFiberOpenEdgeDecidableEq {V : Type*}
    (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

theorem openWalk_transfer_of_edgewise_adjacency
    {V : Type*} (G : SimpleGraph V)
    (C C' : Configuration G) {a b : V}
    (P : (openGraph G C).Walk a b)
    (hstep : ∀ {u v : V}, s(u, v) ∈ P.edges →
      (openGraph G C').Adj u v) :
    ∃ Q : (openGraph G C').Walk a b, Q.support = P.support := by
  induction P with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y z hadj tail ih =>
      have hhead : s(x, y) ∈ (SimpleGraph.Walk.cons hadj tail).edges := by
        simp [SimpleGraph.Walk.edges_cons]
      have htarget := hstep hhead
      obtain ⟨Q, hQ⟩ := ih (by
        intro u v he
        apply hstep
        simp [SimpleGraph.Walk.edges_cons, he])
      exact ⟨SimpleGraph.Walk.cons htarget Q, by simp [hQ]⟩

end
end PottsContinuity.Exploration

namespace PottsContinuity.PlanarMixed.FiniteSlit.RectangleSourceArms

open PottsContinuity.PD.FK
open PottsContinuity.PlanarMixed.FiniteSlit

variable {w h : ℕ} {C : Configuration (rectangleGraph (0, 0) w h)}
    {I J : Set (RectangleVertex (0, 0) w h)}

noncomputable section

local instance sourceTraceRectangleFiberDecidableEq :
    DecidableEq (rectangleGraph (0, 0) w h).edgeSet := Classical.decEq _
local instance sourceTraceHostFiberDecidableEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

end
end PottsContinuity.PlanarMixed.FiniteSlit.RectangleSourceArms
