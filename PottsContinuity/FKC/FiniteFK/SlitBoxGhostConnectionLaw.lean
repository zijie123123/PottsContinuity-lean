-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxGhostConnectionLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxQuotientLaw
public import PottsContinuity.FKC.FiniteFK.WiredGhostConnection
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem slitBoxGhost_no_internal_edge (n : ℕ) :
    ∀ ⦃u v : SlitBoxVertex n⦄, (slitBoxGraph n).Adj u v →
      ¬ (u ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) ∧
         v ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n))) := by
  intro u v hadj ⟨hu, hv⟩
  exact slitBoxGraph_no_adj_on_wiredArc n hu hv hadj

private theorem slitBoxGhost_neighbor_unique (n : ℕ) :
    ∀ ⦃x s t : SlitBoxVertex n⦄,
      x ∉ (slitBoxWiredArc n : Set (SlitBoxVertex n)) →
      s ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) →
      t ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) →
      (slitBoxGraph n).Adj s x → (slitBoxGraph n).Adj t x → s = t := by
  intro x s t hx hs ht hsx htx
  exact slitBoxGraph_adj_wiredArc_unique n hx hs ht hsx.symm htx.symm

/-- The actual connection event from a retained slit-box vertex to the ghost in the
quotient slit graph. -/
def slitBoxGhostConnectionEvent (n : ℕ) (u : SlitBoxVertex n) :
    Set (Configuration (slitBoxGhostGraph n)) :=
  {B | ActualConnected (slitBoxGhostGraph n) B (slitBoxGhostMap n u) none}

/-- Under the configuration map, connecting to the ghost is exactly the
original actual open-path event of hitting the wired arc. -/
theorem slitBoxWiredArcConnectionEvent_preimage (n : ℕ) (u : SlitBoxVertex n) :
    (fun A : Configuration (slitBoxGraph n) =>
      A.map (slitBoxGhostEdgeEquiv n).toEmbedding) ⁻¹'
        slitBoxGhostConnectionEvent n u = slitBoxWiredArcConnectionEvent n u := by
  simpa [slitBoxGhostConnectionEvent, slitBoxGhostGraph, slitBoxGhostMap,
    slitBoxGhostEdgeEquiv, slitBoxWiredArcConnectionEvent] using
    (wiredGhost_connection_preimage
      (slitBoxWiredArc n : Set (SlitBoxVertex n))
      (slitBoxWiredArc_nonempty n) (slitBoxGraph n)
      (slitBoxGhost_no_internal_edge n) (slitBoxGhost_neighbor_unique n) u)

/-- The source wired-arc hitting probability equals the actual ghost-connection
probability under the free law on the collapsed slit graph. -/
theorem slitBoxWiredArcConnectionEvent_measure_eq_ghost
    (n : ℕ) (q : ClusterWeight) (u : SlitBoxVertex n) :
    measure (slitBoxGraph n) q (slitBoxBoundary n)
        (slitBoxWiredArcConnectionEvent n u) =
      measure (slitBoxGhostGraph n) q
        (BoundaryCondition.free (∅ : Set (slitBoxGhostCarrier n)))
        (slitBoxGhostConnectionEvent n u) := by
  classical
  let f : Configuration (slitBoxGraph n) → Configuration (slitBoxGhostGraph n) :=
    fun A => A.map (slitBoxGhostEdgeEquiv n).toEmbedding
  let : MeasurableSpace (Configuration (slitBoxGraph n)) := ⊤
  let : MeasurableSpace (Configuration (slitBoxGhostGraph n)) := ⊤
  have hf : Measurable f := by
    intro s hs
    exact MeasurableSpace.measurableSet_top
  have hmeasure := congrArg
    (fun μ : PMF (Configuration (slitBoxGhostGraph n)) =>
      μ.toMeasure (slitBoxGhostConnectionEvent n u)) (slitBoxLaw_map_ghost n q)
  rw [PMF.toMeasure_map_apply _ _ _ hf MeasurableSpace.measurableSet_top] at hmeasure
  rw [slitBoxWiredArcConnectionEvent_preimage] at hmeasure
  simpa [f, measure] using hmeasure

end
end PottsContinuity.FKC.FiniteFK
