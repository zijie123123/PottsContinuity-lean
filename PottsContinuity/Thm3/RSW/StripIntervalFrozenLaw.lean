module

public import PottsContinuity.Thm3.RSW.FrozenAwayWiring
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalTopBoundary
public import PottsContinuity.FKC.FiniteFK.HorizontalStripConditionalBoundary
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutRectangle
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
local instance stripIntervalFrozenEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

section
variable (a : ℤ) (w n N : ℕ) (hleft : -(N:ℤ)<a) (hright : a+(w:ℤ)<N)
local notation "outer" => FKC.Medial.horizontalStripCutRectangle N n
local notation "core" => FKC.rectangleGraph (a,0) w (2*n)
local notation "inc" => FKC.FiniteFK.horizontalStripIntervalEmbedding (n:=n) hleft.le hright.le
local notation "inc_le" => FKC.FiniteFK.horizontalStripInterval_map_le (n:=n) hleft.le hright.le

/-- The actual retained interval has exactly top-only wiring once observed
open edges lie outside it, for every admissible original boundary partition. -/
theorem stripInterval_frozen_partition_eq_top
    (ξ : BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)))
    (hξ : ξ.boundary ⊆ FKC.FiniteFK.horizontalStripTopSidesSet N n)
    (hTop : (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n)).partition ≤ ξ.partition)
    (A : Configuration outer)
    (hA : ∀ ⦃e : (outer).edgeSet⦄, e ∈ A → ∀ ⦃v : FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)⦄,
      v ∈ e.val → v ∉ Set.range inc) :
    (isolatedExtensionPullbackBoundary inc (frozenBoundary ξ A)).partition =
      (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripIntervalTopWiredSet a w n)).partition := by
  have hξ' : ξ.boundary ⊆ {v | v ∉ Set.range inc} ∪ FKC.FiniteFK.horizontalStripTopWiredSet N n := by
    intro v hv
    have hh := hξ hv
    change v.val.2=(2*n:ℤ) ∨ v.val.1= -(N:ℤ) ∨ v.val.1=(N:ℤ) at hh
    change v ∉ Set.range inc ∨ v.val.2=(2*n:ℤ)
    rcases hh with ht | hl | hr
    · exact Or.inr ht
    all_goals
      left
      rintro ⟨u,hu⟩
      have hc := congrArg (fun z : FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n) => z.val.1) hu
      change u.val.1=v.val.1 at hc
      have hb := (FKC.mem_latticeRectangle (a,0) u.val w (2*n)).mp u.property
      dsimp at hb
      omega
  have hp := frozenAway_partition_eq_wired inc {v | v ∉ Set.range inc}
    (FKC.FiniteFK.horizontalStripTopWiredSet N n) ξ A hξ' hTop hA
    (fun u hu => hu ⟨u,rfl⟩)
  have hpre : inc ⁻¹' FKC.FiniteFK.horizontalStripTopWiredSet N n =
      FKC.FiniteFK.horizontalStripIntervalTopWiredSet a w n := by
    ext u
    rfl
  rw [hpre] at hp
  exact hp

/-- The exact original frozen-state DMP on a retained strip interval,
with the top-only boundary identification proved rather than postulated.
All interior edge probabilities and all real cluster weights q>=1 are allowed. -/
theorem stripInterval_frozen_law_eq_top
    (θ : Parameters)
    (ξ : BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)))
    (hξ : ξ.boundary ⊆ FKC.FiniteFK.horizontalStripTopSidesSet N n)
    (hTop : (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet N n)).partition ≤ ξ.partition)
    (K : RemovedConfiguration outer (subgraphRemovedEdges ((core).map inc) outer))
    (hK : ∀ ⦃e : (outer).edgeSet⦄, e ∈ K.val → ∀ ⦃v : FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n)⦄,
      v ∈ e.val → v ∉ Set.range inc) :
    ((law outer θ ξ).filter
      (frozenStateEvent (subgraphRemovedEdges ((core).map inc) outer) K)
      (frozenStateEvent_support θ ξ _ K)).map
        (embeddedConfigurationRestriction core outer inc inc_le) =
      law core θ (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripIntervalTopWiredSet a w n)) := by
  rw [law_filter_frozen_map_embeddedRestriction core outer inc inc_le θ ξ K]
  exact law_eq_of_boundary_partition_eq θ _ _
    (stripInterval_frozen_partition_eq_top a w n N hleft hright ξ hξ hTop K.val hK)

end
end
end PottsContinuity.RSW
