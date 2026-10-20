-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/PortEmbedding.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.DobrushinPairing
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Actual complex paths for the port pairings

Ports project to the midpoints of their original lattice bonds. Different
flags may have the same position; they are never identified as combinatorial
ports. Local pairings project to constant paths. Interior corner pairings use
the actual straight medial edge within the closure of the corresponding cell.
Exterior caps travel along the two boundary half-edges through their common
primal vertex, without assuming that their exterior cell labels coincide.
This exterior routing is an auxiliary interpolation. A mesh-scale comparison
with a drawn boundary curve and connectors at the marked endpoints are not
formalized here, and no equality of random curve laws is claimed.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set Medial

noncomputable section

namespace Medial.LatticeBond

end Medial.LatticeBond

namespace Medial.LatticePort

end Medial.LatticePort

namespace Medial.DomainPort

variable {δ : PositiveMesh} {D : Set ℂ}

/-- The actual complex midpoint, forgetting flags only at the geometric projection. -/
def position (p : DomainPort δ D) : ℂ := p.toLatticePort.position δ

/-- The local matching changes flags at the same geometric midpoint. -/
def localPath (C : FiniteFK.Configuration (domainLatticeGraph δ D)) (p : DomainPort δ D) :
    Path p.position (localPair C p).position := Path.segment _ _

@[simp] theorem localPath_apply (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (p : DomainPort δ D) (t : unitInterval) : p.localPath C t = p.position := by
  change Path.segment (p.toLatticePort.position δ) ((localPair C p).toLatticePort.position δ) t = _
  rw [localPair_position, Path.segment_same]
  rfl

end Medial.DomainPort

namespace Medial.InteriorPort

variable {δ : PositiveMesh} {D : Set ℂ}

end Medial.InteriorPort

namespace LatticePolygon

variable {m : ℕ} (P : LatticePolygon m)

/-- Truncation either keeps the original cap partner or fixes the port, so it
always preserves the actual primal vertex. -/
theorem truncatedBoundaryCapPair_primalVertex (δ : PositiveMesh)
    (a : ZMod (m + 3)) (k : ℕ) (p : P.SurvivingBoundaryCapPort δ a k) :
    (P.truncatedBoundaryCapPair δ a k p).val.val.toLatticePort.primalVertex =
      p.val.val.toLatticePort.primalVertex := by
  obtain ⟨r, rfl⟩ := (P.survivingBoundaryCapEquiv δ a k).surjective p
  rw [P.truncatedBoundaryCapPair_equiv, P.survivingBoundaryCapEquiv_val,
    P.survivingBoundaryCapEquiv_val]
  by_cases hr : ¬WiredArcIndex a k (boundaryCapPartner r.val).1
  · simp only [truncatedCapPartner, dite_eq_left hr]
    exact P.boundaryCapPort_partner_primalVertex δ r.val
  · simp only [truncatedCapPartner, dite_eq_right hr]

/-- Both retained geometric rules preserve the same actual primal vertex. -/
theorem retainedGeometryPair_primalVertex (δ : PositiveMesh)
    (a : ZMod (m + 3)) (k : ℕ) (p : P.RetainedPort δ a k) :
    (P.retainedGeometryPair δ a k p).val.toLatticePort.primalVertex =
      p.val.toLatticePort.primalVertex := by
  obtain ⟨q, rfl⟩ := (P.retainedPortSplitEquiv δ a k).symm.surjective p
  cases q with
  | inl q =>
    simp only [P.retainedPortSplitEquiv_symm_inl, P.retainedGeometryPair_interior,
      P.retainedPortOfInterior_val]
    exact q.cornerPair_primalVertex
  | inr q =>
    simp only [P.retainedPortSplitEquiv_symm_inr, P.retainedGeometryPair_boundaryCap,
      P.retainedPortOfBoundaryCap_val]
    exact P.truncatedBoundaryCapPair_primalVertex δ a k q

end LatticePolygon

end
end PottsContinuity.FKC
