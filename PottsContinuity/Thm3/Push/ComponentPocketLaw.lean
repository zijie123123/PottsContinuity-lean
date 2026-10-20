module

public import PottsContinuity.Thm3.Push.WiredPocketBoundary
public import PottsContinuity.PlanarMixed.Square.Extras
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PlanarMixed.Square
noncomputable section
local instance componentPocketEdgeEq {V : Type*} (H : SimpleGraph V) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Distinct free pockets may attach to distinct retained classes. An anchor
is assigned per actual deleted component, preserving the other wired classes. -/
theorem componentPocket_frozen_partition {V : Type*} [Finite V]
    (H : SimpleGraph V) (S : Set V) (ξ : BoundaryCondition V)
    (anchor : (H.induce Sᶜ).ConnectedComponent → S)
    (hfree : ∀ x y, x ∉ S → ξ.partition.r x y → x = y)
    (hattach : ∀ (x : {v : V // v ∉ S}) (y : S), H.Adj x.val y.val →
      ξ.partition.r (anchor ((H.induce Sᶜ).connectedComponentMk x)).val y.val)
    (K : RemovedConfiguration H (subgraphRemovedEdges ((H.induce S).map (pocketInclusion S)) H)) :
    (isolatedExtensionPullbackBoundary (pocketInclusion S) (frozenBoundary ξ K.val)).partition =
      (isolatedExtensionPullbackBoundary (pocketInclusion S) ξ).partition := by
  classical
  let f := pocketInclusion S
  let r : V → S := fun v => if hv : v ∈ S then ⟨v,hv⟩ else
    anchor ((H.induce Sᶜ).connectedComponentMk ⟨v,hv⟩)
  let η := (isolatedExtensionPullbackBoundary f ξ).partition
  have hr : ∀ u : S, r (f u) = u := by
    intro u
    simp only [r,f,pocketInclusion,Function.Embedding.coeFn_mk,dite_eq_left u.property]
  have hboundary : ∀ x y, ξ.partition.r x y → η.r (r x) (r y) := by
    intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · change ξ.partition.r (r x).val (r y).val
        simpa only [r,dite_eq_left hx,dite_eq_left hy] using hxy
      · have he := hfree y x hy (ξ.partition.symm hxy)
        subst y
        exact η.refl _
    · have he := hfree x y hx hxy
      subst y
      exact η.refl _
  have hopen : ∀ x y, (openGraph H K.val).Adj x y → η.r (r x) (r y) := by
    intro x y hxy
    have hH := openGraph_le H K.val hxy
    have hn : ¬(x ∈ S ∧ y ∈ S) := by
      rintro ⟨hx,hy⟩
      obtain ⟨e,he,hev⟩ := (openGraph_adj H K.val x y).mp hxy
      have hremoved := (mem_subgraphRemovedEdges e).mp (K.property he)
      apply hremoved
      rw [hev]
      apply ((H.induce S).map f).mem_edgeSet.mpr
      exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨⟨x,hx⟩,⟨y,hy⟩,hH,rfl,rfl⟩
    change ξ.partition.r (r x).val (r y).val
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · exact False.elim (hn ⟨hx,hy⟩)
    · simpa only [r,dite_eq_left hx,dite_eq_right hy] using
        ξ.partition.symm (hattach ⟨y,hy⟩ ⟨x,hx⟩ hH.symm)
    · simpa only [r,dite_eq_right hx,dite_eq_left hy] using
        hattach ⟨x,hx⟩ ⟨y,hy⟩ hH
    · have heq : (H.induce Sᶜ).connectedComponentMk ⟨x,hx⟩ =
          (H.induce Sᶜ).connectedComponentMk ⟨y,hy⟩ :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (H.induce Sᶜ).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hH)
      simp only [r,dite_eq_right hx,dite_eq_right hy,heq]
      exact ξ.partition.refl _
  exact isolatedExtensionPullback_frozenBoundary_partition_eq_of_retraction
    f r hr ξ K.val η hboundary hopen (fun _ _ h => h)

/-- Integrating each pocket preserves the exact retained FK law, even when
separate pockets are assigned to different boundary classes. -/
theorem componentPocket_law_map
    {V : Type*} [Finite V]
    (H : SimpleGraph V) (θ : Parameters) (S : Set V) (ξ : BoundaryCondition V)
    (anchor : (H.induce Sᶜ).ConnectedComponent → S)
    (hfree : ∀ x y, x ∉ S → ξ.partition.r x y → x = y)
    (hattach : ∀ (x : {v : V // v ∉ S}) (y : S), H.Adj x.val y.val →
      ξ.partition.r (anchor ((H.induce Sᶜ).connectedComponentMk x)).val y.val) :
    (law H θ ξ).map
      (embeddedConfigurationRestriction (H.induce S) H (pocketInclusion S)
        (pocketInduced_map_le H S)) =
    law (H.induce S) θ (isolatedExtensionPullbackBoundary (pocketInclusion S) ξ) := by
  apply law_embeddedConfigurationRestriction_eq_of_frozen_partition
  intro K
  exact componentPocket_frozen_partition H S ξ anchor hfree hattach K

/-- A geometric no-bridge condition suffices: two retained attachments to
one deleted component must already lie in the same boundary class. -/
theorem componentPocket_frozen_partition_of_no_bridge {V : Type*} [Finite V]
    (H : SimpleGraph V) (S : Set V) (ξ : BoundaryCondition V) (a : S)
    (hfree : ∀ x y, x ∉ S → ξ.partition.r x y → x = y)
    (hnoBridge : ∀ (x y : {v : V // v ∉ S}), (H.induce Sᶜ).Reachable x y →
      ∀ u v : S, H.Adj x.val u.val → H.Adj y.val v.val → ξ.partition.r u.val v.val)
    (K : RemovedConfiguration H (subgraphRemovedEdges ((H.induce S).map (pocketInclusion S)) H)) :
    (isolatedExtensionPullbackBoundary (pocketInclusion S) (frozenBoundary ξ K.val)).partition =
      (isolatedExtensionPullbackBoundary (pocketInclusion S) ξ).partition := by
  classical
  let attach : (H.induce Sᶜ).ConnectedComponent → Set S := fun c =>
    {u | ∃ x : {v : V // v ∉ S}, (H.induce Sᶜ).connectedComponentMk x = c ∧ H.Adj x.val u.val}
  let anchor : (H.induce Sᶜ).ConnectedComponent → S := fun c =>
    if h : (attach c).Nonempty then h.choose else a
  apply componentPocket_frozen_partition H S ξ anchor hfree
  intro x y hxy
  let c := (H.induce Sᶜ).connectedComponentMk x
  have hnonempty : (attach c).Nonempty := ⟨y,x,rfl,hxy⟩
  have hs : anchor c ∈ attach c := by
    simp only [anchor,dite_eq_left hnonempty]
    exact hnonempty.choose_spec
  obtain ⟨z,hz,hzy⟩ := hs
  have hconn : (H.induce Sᶜ).Reachable z x :=
    SimpleGraph.ConnectedComponent.exact hz
  exact hnoBridge z x hconn (anchor c) y hzy hxy

/-- The exact retained marginal follows from free deleted vertices and
absence of a deleted-component bridge between distinct retained classes. -/
theorem componentPocket_law_map_of_no_bridge
    {V : Type*} [Finite V]
    (H : SimpleGraph V) (θ : Parameters) (S : Set V) (ξ : BoundaryCondition V) (a : S)
    (hfree : ∀ x y, x ∉ S → ξ.partition.r x y → x = y)
    (hnoBridge : ∀ (x y : {v : V // v ∉ S}), (H.induce Sᶜ).Reachable x y →
      ∀ u v : S, H.Adj x.val u.val → H.Adj y.val v.val → ξ.partition.r u.val v.val) :
    (law H θ ξ).map
      (embeddedConfigurationRestriction (H.induce S) H (pocketInclusion S)
        (pocketInduced_map_le H S)) =
    law (H.induce S) θ (isolatedExtensionPullbackBoundary (pocketInclusion S) ξ) := by
  apply law_embeddedConfigurationRestriction_eq_of_frozen_partition
  intro K
  exact componentPocket_frozen_partition_of_no_bridge H S ξ a hfree hnoBridge K

end
end PottsContinuity.Push
