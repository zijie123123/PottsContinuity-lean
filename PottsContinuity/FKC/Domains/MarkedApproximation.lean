-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/MarkedApproximation.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.MarkedBoundary
public import PottsContinuity.FKC.Domains.PolygonDomain
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Marked lattice approximation sequences

These are the data of a marked Jordan domain approximated by marked lattice
domains. Every discrete
domain is the actual interior of an embedded nearest-neighbor lattice polygon;
its two marks are specified distinct polygon vertices. Both the discrete and
limiting boundary parametrizations are arbitrary admissible counterclockwise
parametrizations. The mesh tends to zero, without a monotonicity condition, and
the genuine uniform distance between those parametrizations tends to zero.

This file defines neither a medial strand nor a scaling-limit law. The two
parameter half-arcs are identified with the polygon's cyclic arcs, possibly
exchanged, in `FKC.Domains.MarkedPolygonOrientation`
(`LatticePolygon.exists_markedBoundaryParametrization_arc_pair`); by
`MarkedBoundaryParametrization.half_arcs_eq` in `FKC.Domains.MarkedHalfArcs` they do
not depend on the chosen counterclockwise parametrization.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set Filter Topology
open scoped unitInterval

noncomputable section

/-- One marked lattice boundary at a positive mesh, with an arbitrary admissible
counterclockwise parametrization of its actual derived domain. -/
structure MarkedLatticeBoundary where
  mesh : PositiveMesh
  size : ℕ
  polygon : LatticePolygon size
  first : ZMod (size + 3)
  second : ZMod (size + 3)
  marks_ne : first ≠ second
  boundary : MarkedBoundaryParametrization (polygon.markedDomain mesh first second marks_ne)

namespace MarkedLatticeBoundary

/-- The domain and marks come from the actual embedded lattice polygon. -/
def markedDomain (B : MarkedLatticeBoundary) : MarkedJordanDomain :=
  B.polygon.markedDomain B.mesh B.first B.second B.marks_ne

@[simp] theorem markedDomain_domain (B : MarkedLatticeBoundary) :
    B.markedDomain.domain = B.polygon.domain B.mesh := rfl

@[simp] theorem markedDomain_a (B : MarkedLatticeBoundary) :
    B.markedDomain.a = latticeEmbed B.mesh (B.polygon.vertex B.first) := rfl

@[simp] theorem markedDomain_b (B : MarkedLatticeBoundary) :
    B.markedDomain.b = latticeEmbed B.mesh (B.polygon.vertex B.second) := rfl

end MarkedLatticeBoundary

/-- The exact marked boundary approximation data, using the uniform metric on
continuous maps of the fixed unit interval, before any random strand is defined. -/
structure MarkedApproximationSequence (D : MarkedJordanDomain) where
  boundary : MarkedBoundaryParametrization D
  discrete : ℕ → MarkedLatticeBoundary
  mesh_tendsto : Tendsto (fun n => ((discrete n).mesh : ℝ)) atTop (𝓝 0)
  uniform_tendsto : Tendsto
    (fun n => dist (discrete n).boundary.path.toContinuousMap boundary.path.toContinuousMap)
    atTop (𝓝 0)

namespace MarkedApproximationSequence

variable {D : MarkedJordanDomain}

end MarkedApproximationSequence

end

end PottsContinuity.FKC
