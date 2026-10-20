-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FrozenBoundaryRetraction.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import PottsContinuity.FKC.FiniteFK.IsolatedBoundaryComponents
public import PottsContinuity.FKC.FiniteFK.DomainMarkov

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V U : Type*} {G : SimpleGraph V}

/-- A retraction transports every actual open connection and every original
boundary identification into a target setoid on the retained vertices. -/
theorem componentSetoid_comap_le_of_retraction
    (f : U ↪ V) (r : V → U) (hr : ∀ u, r (f u) = u)
    (ξ : BoundaryCondition V) (A : Configuration G) (η : Setoid U)
    (hξ : ∀ x y, ξ.partition.r x y → η.r (r x) (r y))
    (hopen : ∀ x y, (openGraph G A).Adj x y → η.r (r x) (r y)) :
    Setoid.comap f (componentSetoid G ξ A) ≤ η := by
  have hcomp : componentSetoid G ξ A ≤ Setoid.comap r η := by
    apply componentSetoid_le
    · apply reachableSetoid_le_of_adj (openGraph G A) (Setoid.comap r η)
      intro x y hxy
      exact (Setoid.comap_rel r η x y).mpr (hopen x y hxy)
    · intro x y hxy
      exact (Setoid.comap_rel r η x y).mpr (hξ x y hxy)
  intro u v huv
  have hfv : (componentSetoid G ξ A).r (f u) (f v) :=
    (Setoid.comap_rel f (componentSetoid G ξ A) u v).mp huv
  have hη := hcomp hfv
  change η.r (r (f u)) (r (f v)) at hη
  rw [hr u, hr v] at hη
  exact hη

/-- If the target relation also follows from the original boundary partition,
then the pulled-back frozen partition is exactly that target relation. -/
theorem isolatedExtensionPullback_frozenBoundary_partition_eq_of_retraction
    (f : U ↪ V) (r : V → U) (hr : ∀ u, r (f u) = u)
    (ξ : BoundaryCondition V) (A : Configuration G) (η : Setoid U)
    (hξ : ∀ x y, ξ.partition.r x y → η.r (r x) (r y))
    (hopen : ∀ x y, (openGraph G A).Adj x y → η.r (r x) (r y))
    (hlower : η ≤ Setoid.comap f ξ.partition) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ A)).partition = η := by
  apply Setoid.ext
  intro u v
  change (componentSetoid G ξ A).r (f u) (f v) ↔ η.r u v
  constructor
  · intro huv
    exact componentSetoid_comap_le_of_retraction f r hr ξ A η hξ hopen
      ((Setoid.comap_rel f (componentSetoid G ξ A) u v).mpr huv)
  · intro huv
    exact boundary_component G ξ A (hlower huv)

end
end PottsContinuity.FKC.FiniteFK
