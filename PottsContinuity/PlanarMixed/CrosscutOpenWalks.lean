module

public import PottsContinuity.PlanarMixed.CrosscutBand
public import PottsContinuity.PlanarMixed.EmbeddedActiveLaw

/-! The actual frozen-open crosscuts induce the necessary arc wiring.
Only sampled open walks are used; boundary identifications create no paths.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- Forget that a walk's bonds are open, without changing its vertices. -/
def openWalkUnderlying {V : Type*} (G : SimpleGraph V) (K : Configuration G)
    {a b : V} (p : (openGraph G K).Walk a b) : G.Walk a b :=
  p.map { toFun := id, map_rel' := fun h => openGraph_le G K h }

@[simp] theorem openWalkUnderlying_support {V : Type*} (G : SimpleGraph V)
    (K : Configuration G) {a b : V} (p : (openGraph G K).Walk a b) :
    (openWalkUnderlying G K p).support = p.support := by
  unfold openWalkUnderlying
  have h := SimpleGraph.Walk.support_map
    ({ toFun := id, map_rel' := fun h => openGraph_le G K h } : openGraph G K →g G) p
  exact h.trans (by change p.support.map id = p.support; exact List.map_id _)

/-- Forgetting open-state proofs preserves disjoint trace supports. -/
theorem openWalkUnderlying_disjoint {V : Type*} (G : SimpleGraph V)
    (K : Configuration G) {a b c d : V}
    (p : (openGraph G K).Walk a b) (q : (openGraph G K).Walk c d)
    (h : ∀ z ∈ p.support, z ∉ q.support) :
    ∀ z ∈ (openWalkUnderlying G K p).support,
      z ∉ (openWalkUnderlying G K q).support := by
  simpa only [openWalkUnderlying_support] using h

/-- Any two vertices on one actual open walk are actually connected. -/
theorem openWalk_support_actualConnected {V : Type*} (G : SimpleGraph V)
    (K : Configuration G) {a b v w : V} (p : (openGraph G K).Walk a b)
    (hv : v ∈ p.support) (hw : w ∈ p.support) : ActualConnected G K v w := by
  classical
  exact ⟨(p.takeUntil v hv).reverse.append (p.takeUntil w hw)⟩

end
end PottsContinuity.PlanarMixed
