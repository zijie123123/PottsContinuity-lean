module

public import PottsContinuity.PlanarMixed.OmegaInterfaces
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Finite deterministic certificates for the extremal boundary comparison

The universal quantifier over exterior configurations is equivalent to ONE
maximally open exterior state. A separating equivalence relation preserved by
each exterior edge and by the reference boundary then certifies that state.
For the ranked bands between two ordered crosscuts the relation is constructed in
`PlanarMixed.RankedBand` (`rankedBand_extremalBoundaryComparison`).
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK
noncomputable section

/-- Only the full exterior graph needs to be checked: every actual exterior
record induces a finer partition by the proved component monotonicity. -/
theorem extremalBoundaryComparison_iff_fullExterior
    {V : Type*} [Finite V]
    (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
    (Ω : SimpleGraph V) (f : V ↪ RectangleVertex a N N)
    (η : BoundaryCondition V) :
    ExtremalBoundaryComparison a N hN Ω f η ↔
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary (squareSeparateLeftRightBoundary a N hN)
          (subgraphRemovedEdges (Ω.map f) (rectangleGraph a N N)))).partition ≤
        η.partition := by
  constructor
  · intro h
    exact h ⟨_, Finset.Subset.refl _⟩
  · intro h K u v huv
    apply h
    change (componentSetoid (rectangleGraph a N N)
      (squareSeparateLeftRightBoundary a N hN) K.val).r (f u) (f v) at huv
    exact componentSetoid_mono_edges_boundary _ _ le_rfl _ _ K.property huv

/-- A local deterministic separation certificate discharges the ENTIRE
exterior-partition interface: exterior edges and original wiring preserve
sigma, and its pullback is bounded by the actual Omega boundary. -/
theorem extremalBoundaryComparison_of_exteriorSeparation
    {V : Type*} [Finite V]
    (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
    (Ω : SimpleGraph V) (f : V ↪ RectangleVertex a N N)
    (η : BoundaryCondition V) (σ : Setoid (RectangleVertex a N N))
    (href : (squareSeparateLeftRightBoundary a N hN).partition ≤ σ)
    (hcut : ∀ ⦃u v : RectangleVertex a N N⦄,
      (openGraph (rectangleGraph a N N)
        (subgraphRemovedEdges (Ω.map f) (rectangleGraph a N N))).Adj u v → σ.r u v)
    (hpull : Setoid.comap f σ ≤ η.partition) :
    ExtremalBoundaryComparison a N hN Ω f η := by
  apply (extremalBoundaryComparison_iff_fullExterior a N hN Ω f η).mpr
  have hcomp : componentSetoid (rectangleGraph a N N)
      (squareSeparateLeftRightBoundary a N hN)
      (subgraphRemovedEdges (Ω.map f) (rectangleGraph a N N)) ≤ σ := by
    apply componentSetoid_le
    · intro u v hconn
      obtain ⟨p⟩ := (actualConnected_iff_walk _ _ u v).mp hconn
      induction p with
      | nil => exact σ.refl _
      | @cons u v w huv p ih => exact σ.trans (hcut huv) (ih p.reachable)
    · exact href
  intro u v huv
  exact hpull (hcomp huv)

end
end PottsContinuity.PlanarMixed
