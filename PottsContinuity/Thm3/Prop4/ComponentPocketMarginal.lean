module

public import PottsContinuity.Thm3.Push.WiredPocketBoundary
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Exact retained-component marginal with one attached boundary class -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push PlanarMixed.Square
noncomputable section
local instance componentPocketEdgeEq {V : Type*} (H : SimpleGraph V) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Averaging the other edge components creates no new retained boundary
join when all external boundary attachments use one retained class. -/
theorem componentPocket_frozen_partition {V : Type*} [Finite V]
    (H : SimpleGraph V) (S : Set V) (ξ : BoundaryCondition V) (a : S)
    (hclosed : ∀ x ∈ S, ∀ y, H.Adj x y → y ∈ S)
    (hboundary : ∀ x ∈ S, ∀ y, y ∉ S → ξ.partition.r x y → ξ.partition.r x a.val)
    (K : RemovedConfiguration H (subgraphRemovedEdges ((H.induce S).map (pocketInclusion S)) H)) :
    (isolatedExtensionPullbackBoundary (pocketInclusion S) (frozenBoundary ξ K.val)).partition =
      (isolatedExtensionPullbackBoundary (pocketInclusion S) ξ).partition := by
  classical
  let f := pocketInclusion S
  let r := wiredPocketRetraction S a
  let η := (isolatedExtensionPullbackBoundary f ξ).partition
  have hr : ∀ u : S, r (f u) = u := by
    intro u
    change wiredPocketRetraction S a u.val = u
    simp only [wiredPocketRetraction,dite_eq_left u.property]
  have hξ : ∀ x y, ξ.partition.r x y → η.r (r x) (r y) := by
    intro x y hxy
    change ξ.partition.r (r x).val (r y).val
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simpa only [r,wiredPocketRetraction,dite_eq_left hx,dite_eq_left hy] using hxy
    · simpa only [r,wiredPocketRetraction,dite_eq_left hx,dite_eq_right hy] using hboundary x hx y hy hxy
    · simpa only [r,wiredPocketRetraction,dite_eq_right hx,dite_eq_left hy] using
        ξ.partition.symm (hboundary y hy x hx (ξ.partition.symm hxy))
    · simp only [r,wiredPocketRetraction,dite_eq_right hx,dite_eq_right hy]
      exact ξ.partition.refl _
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
    have hx : x ∉ S := fun hx => hn ⟨hx,hclosed x hx y hH⟩
    have hy : y ∉ S := fun hy => hn ⟨hclosed y hy x hH.symm,hy⟩
    simp only [r,wiredPocketRetraction,dite_eq_right hx,dite_eq_right hy]
    exact η.refl _
  exact isolatedExtensionPullback_frozenBoundary_partition_eq_of_retraction
    f r hr ξ K.val η hξ hopen (fun _ _ h => h)

/-- Integrating all other edge components leaves exactly the actual retained
component FK law. The exterior boundary classes may be arbitrary. -/
theorem componentPocket_law_map {V : Type*} [Finite V]
    (H : SimpleGraph V) (θ : Parameters) (S : Set V) (ξ : BoundaryCondition V) (a : S)
    (hclosed : ∀ x ∈ S, ∀ y, H.Adj x y → y ∈ S)
    (hboundary : ∀ x ∈ S, ∀ y, y ∉ S → ξ.partition.r x y → ξ.partition.r x a.val) :
    (law H θ ξ).map
      (embeddedConfigurationRestriction (H.induce S) H (pocketInclusion S) (pocketInduced_map_le H S)) =
      law (H.induce S) θ (isolatedExtensionPullbackBoundary (pocketInclusion S) ξ) := by
  apply law_embeddedConfigurationRestriction_eq_of_frozen_partition
  intro K
  exact componentPocket_frozen_partition H S ξ a hclosed hboundary K

end
end PottsContinuity.Thm3.Prop4
