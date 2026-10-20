module

public import PottsContinuity.PlanarMixed.Square.Consumers
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Explicit interfaces for the conditioned extremal-path domain

These are predicates on actual finite graph data, not assertions that arbitrary
four marked sets are polygon arcs. Providers must construct the source domain,
its ordered boundary arcs, and the actual dual carrier. No geometry or FK law
is obtained merely by packaging the data in one of these predicates.

DCST TeX L1229-L1235. The square-comparison route only needs the last two
predicates; it does not need a new polygon Euler proof.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- The precise reference-square boundary used in the Omega comparison. -/
abbrev squareSeparateLeftRightBoundary (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N) :=
  twoBlockBoundary (Square.squareLeftArc a N) (Square.squareRightArc a N)
    (Square.squareLeftArc_disjoint_right a N hN)

/-- EVERY state of the removed reference-square edges induces no more wiring
on Omega than the specified Omega boundary. This is a geometric partition
order, not the desired probability lower bound. -/
def ExtremalBoundaryComparison {V : Type*} [Finite V]
    (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
    (Ω : SimpleGraph V) (f : V ↪ RectangleVertex a N N)
    (η : BoundaryCondition V) : Prop :=
  ∀ K : RemovedConfiguration (rectangleGraph a N N)
      (subgraphRemovedEdges (Ω.map f) (rectangleGraph a N N)),
    (isolatedExtensionPullbackBoundary f
      (frozenBoundary (squareSeparateLeftRightBoundary a N hN) K.val)).partition ≤
      η.partition

/-- Deterministic path surgery: every actual square left-right crossing leaves
an actual A-to-C connection in the exact embedded restriction to Omega. -/
def SquareCrossingRestrictsToArcs {V : Type*} [Finite V]
    (a : LatticeVertex) (N : ℕ) (Ω : SimpleGraph V)
    (f : V ↪ RectangleVertex a N N) (hΩ : Ω.map f ≤ rectangleGraph a N N)
    (A C : Set V) : Prop :=
  ∀ ω : Configuration (rectangleGraph a N N),
    ω ∈ arcsConnectionEvent (rectangleGraph a N N)
      (Square.squareLeftArc a N) (Square.squareRightArc a N) →
    embeddedConfigurationRestriction Ω (rectangleGraph a N N) f hΩ ω ∈
      arcsConnectionEvent Ω A C

/-- The exact law on a realized extremal exploration fiber, pushed to the
actual Omega edges. The event must be the source fiber, not an arbitrary
conditioning event asserted to have the desired law. -/
def ExtremalConditionalLaw {U V : Type*} [Finite U] [Finite V]
    (q : Set.Ici (1 : ℝ)) (H : SimpleGraph U) (Ω : SimpleGraph V)
    (ξ : BoundaryCondition U) (η : BoundaryCondition V)
    (F : Set (Configuration H))
    (hF : ∃ C ∈ F, C ∈ (law H (criticalParameters q) ξ).support)
    (r : Configuration H → Configuration Ω) : Prop :=
  ((law H (criticalParameters q) ξ).filter F hF).map r =
    law Ω (criticalParameters q) η

end
end PottsContinuity.PlanarMixed
