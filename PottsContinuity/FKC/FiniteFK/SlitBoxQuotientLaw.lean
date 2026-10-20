-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxQuotientLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxArcGeometry
public import PottsContinuity.FKC.FiniteFK.WiredVertexCollapse
public import PottsContinuity.FKC.FiniteFK.WiredVertexQuotientLaw
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The ghost carrier for the slit box, with the retained wired arc collapsed. -/
abbrev slitBoxGhostCarrier (n : ℕ) :=
  WiredVertexCarrier (slitBoxWiredArc n : Set (SlitBoxVertex n))

 theorem slitBoxWiredArc_no_internal_edge (n : ℕ) :
    ∀ ⦃u v : SlitBoxVertex n⦄, (slitBoxGraph n).Adj u v →
      ¬ (u ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) ∧
         v ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n))) := by
  intro u v hadj ⟨hu, hv⟩
  exact slitBoxGraph_no_adj_on_wiredArc n hu hv hadj

 theorem slitBoxWiredArc_neighbor_unique (n : ℕ) :
    ∀ ⦃x s t : SlitBoxVertex n⦄,
      x ∉ (slitBoxWiredArc n : Set (SlitBoxVertex n)) →
      s ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) →
      t ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) →
      (slitBoxGraph n).Adj s x → (slitBoxGraph n).Adj t x → s = t := by
  intro x s t hx hs ht hsx htx
  exact slitBoxGraph_adj_wiredArc_unique n hx hs ht hsx.symm htx.symm

/-- The simple graph on the ghost carrier induced from the slit-box edges. -/
def slitBoxGhostGraph (n : ℕ) : SimpleGraph (slitBoxGhostCarrier n) :=
  wiredVertexGraph (slitBoxWiredArc n : Set (SlitBoxVertex n))
    (slitBoxWiredArc_nonempty n) (slitBoxGraph n)
    (slitBoxWiredArc_no_internal_edge n)

/-- The explicit vertex map sends the wired arc to `none` and retains every
other slit-box vertex as an `Option.some`. -/
def slitBoxGhostMap (n : ℕ) : SlitBoxVertex n → slitBoxGhostCarrier n :=
  wiredVertexMap (slitBoxWiredArc n : Set (SlitBoxVertex n))
    (slitBoxWiredArc_nonempty n)

/-- The exact edge correspondence from the slit graph to the ghost graph. -/
def slitBoxGhostEdgeEquiv (n : ℕ) :
    (slitBoxGraph n).edgeSet ≃ (slitBoxGhostGraph n).edgeSet :=
  wiredVertexEdgeEquiv (slitBoxWiredArc n : Set (SlitBoxVertex n))
    (slitBoxWiredArc_nonempty n) (slitBoxGraph n)
    (slitBoxWiredArc_no_internal_edge n) (slitBoxWiredArc_neighbor_unique n)

@[simp] theorem slitBoxGhostEdgeEquiv_val (n : ℕ)
    (e : (slitBoxGraph n).edgeSet) :
    (slitBoxGhostEdgeEquiv n e).val = Sym2.map (slitBoxGhostMap n) e.val := rfl

theorem slitBoxGhostMap_surjective (n : ℕ) :
    Function.Surjective (slitBoxGhostMap n) :=
  wiredVertexMap_surjective _ _

theorem slitBoxBoundary_partition_eq_ker (n : ℕ) :
    (slitBoxBoundary n).partition = Setoid.ker (slitBoxGhostMap n) := by
  exact wired_boundary_partition_eq_ker _ _

/-- The free FK law on the graph with the retained arc collapsed to one ghost
vertex is the image of the slit-box FK law wired on that arc. -/
theorem slitBoxLaw_map_ghost (n : ℕ) (q : ClusterWeight) :
    (law (slitBoxGraph n) q (slitBoxBoundary n)).map
        (fun A => A.map (slitBoxGhostEdgeEquiv n).toEmbedding) =
      law (slitBoxGhostGraph n) q
        (BoundaryCondition.free (∅ : Set (slitBoxGhostCarrier n))) := by
  exact wiredVertexQuotient_law_map (slitBoxGhostMap n)
    (slitBoxGhostMap_surjective n) (slitBoxGhostEdgeEquiv n)
    (slitBoxGhostEdgeEquiv_val n) (slitBoxBoundary n)
    (slitBoxBoundary_partition_eq_ker n) q

end
end PottsContinuity.FKC.FiniteFK
