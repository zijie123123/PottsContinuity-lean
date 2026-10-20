-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteRegionSourceEvent.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingRegionComparison
public import PottsContinuity.FKC.FiniteFK.WiredAvoidingPathCharacterization
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- The literal finite source event: `x` connects to the wired set `W`, and
any actual open walk from outside `H` to `x` visits `W`. -/
def finiteRegionSourceEvent (H W : Set V) (x : V) : Set (Configuration G) :=
  {A | (∃ w ∈ W, ActualConnected G A x w) ∧
    ∀ u, u ∉ H → ∀ p : (openGraph G A).Walk u x,
      ∃ z ∈ p.support, z ∈ W}

/-- The blocking condition for walks from outside the region is exactly
exclusion from the masked cluster rooted at every vertex outside `H`. -/
theorem finiteRegionSourceEvent_blocker_iff_cluster_exclusion
    (H W : Set V) (A : Configuration G) (x : V) :
    (∀ u, u ∉ H → ∀ p : (openGraph G A).Walk u x,
      ∃ z ∈ p.support, z ∈ W) ↔
      x ∉ wiredAvoidingClusterSet G W (wiredAvoidingRegionSeeds H) A := by
  constructor
  · intro hblock hcluster
    rcases (wiredAvoidingClusterConnected_iff_walk_avoiding W
      (wiredAvoidingRegionSeeds H) A x).mp hcluster with ⟨u, hu, p, hp⟩
    obtain ⟨z, hz, hzW⟩ := hblock u
      ((wiredAvoidingRegionSeeds_mem H u).mp hu) p
    exact hp z hz hzW
  · intro hcluster u hu p
    by_contra hnot
    have hp : ∀ z ∈ p.support, z ∉ W := by
      intro z hz hzW
      exact hnot ⟨z, hz, hzW⟩
    have hconn : wiredAvoidingClusterConnected G W
        (wiredAvoidingRegionSeeds H) A x :=
      (wiredAvoidingClusterConnected_iff_walk_avoiding W
        (wiredAvoidingRegionSeeds H) A x).mpr
        ⟨u, (wiredAvoidingRegionSeeds_mem H u).mpr hu, p, hp⟩
    exact hcluster hconn

/-- Source-event membership is precisely a connection to `W` together with
exclusion from the masked outside-`H` cluster. No assumption `W ⊆ H` is needed. -/
theorem finiteRegionSourceEvent_mem_iff
    (H W : Set V) (x : V) (A : Configuration G) :
    A ∈ finiteRegionSourceEvent H W x ↔
      (∃ w ∈ W, ActualConnected G A x w) ∧
      x ∉ wiredAvoidingClusterSet G W (wiredAvoidingRegionSeeds H) A := by
  simp only [finiteRegionSourceEvent, Set.mem_ofPred_eq]
  rw [finiteRegionSourceEvent_blocker_iff_cluster_exclusion]

end
end PottsContinuity.FKC.FiniteFK
