-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/DobrushinPairing.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.DobrushinPorts
public import PottsContinuity.FKC.Medial.PairingGraph

/-!
# Actual geometric pairing and a unique finite two-terminal port path

Interior ports use the genuine square-corner pairing; surviving exterior ports
use the truncated cyclic cap pairing. These proved constituents supply the
geometric involution and its exactly two fixed ports. Together with the actual
configuration's local pairing, the finite layered graph therefore has a unique
simple path from the selected wired arc's start to its finish.

The direction here is explicitly wired-start to wired-finish. The path from the
first mark to the second, which is this path or its reverse, is obtained in
`FKC.Domains.DobrushinInterface` (`MarkedLatticeBoundary.interfaceGraph_existsUnique_isPath`).
This module does not assert a scaling limit or identify an SLE/CLE law.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Medial

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

/-- The two genuine geometric rules on the proved disjoint interior/exterior carriers. -/
def geometryOnRetainedSplit (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    InteriorPort δ (P.domain δ) ⊕ P.SurvivingBoundaryCapPort δ a k →
      InteriorPort δ (P.domain δ) ⊕ P.SurvivingBoundaryCapPort δ a k
  | Sum.inl p => Sum.inl p.cornerPair
  | Sum.inr p => Sum.inr (P.truncatedBoundaryCapPair δ a k p)

theorem geometryOnRetainedSplit_involutive (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) : Function.Involutive (P.geometryOnRetainedSplit δ a k) := by
  rintro (p | p)
  · exact congrArg Sum.inl (InteriorPort.cornerPair_involutive p)
  · exact congrArg Sum.inr (P.truncatedBoundaryCapPair_involutive δ a k p)

theorem geometryOnRetainedSplit_fixed_iff (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (p : InteriorPort δ (P.domain δ) ⊕ P.SurvivingBoundaryCapPort δ a k) :
    P.geometryOnRetainedSplit δ a k p = p ↔
      p = Sum.inr (P.survivingBoundaryCapEquiv δ a k (capStartTerminal a hk2)) ∨
      p = Sum.inr (P.survivingBoundaryCapEquiv δ a k (capFinishTerminal a hk2)) := by
  cases p with
  | inl p => simp [geometryOnRetainedSplit, InteriorPort.cornerPair_ne]
  | inr p =>
    simpa only [geometryOnRetainedSplit, Sum.inr.injEq] using
      P.truncatedBoundaryCapPair_fixed_iff δ a hk1 hk2 p

/-- The actual geometric pairing on every retained port, using the proved exact split. -/
def retainedGeometryPair (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (p : P.RetainedPort δ a k) : P.RetainedPort δ a k :=
  (P.retainedPortSplitEquiv δ a k).symm
    (P.geometryOnRetainedSplit δ a k (P.retainedPortSplitEquiv δ a k p))

@[simp] theorem retainedPortSplitEquiv_geometryPair (δ : PositiveMesh)
    (a : ZMod (m + 3)) (k : ℕ) (p : P.RetainedPort δ a k) :
    P.retainedPortSplitEquiv δ a k (P.retainedGeometryPair δ a k p) =
      P.geometryOnRetainedSplit δ a k (P.retainedPortSplitEquiv δ a k p) := by
  simp [retainedGeometryPair]

theorem retainedGeometryPair_involutive (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) : Function.Involutive (P.retainedGeometryPair δ a k) := by
  intro p
  apply (P.retainedPortSplitEquiv δ a k).injective
  rw [P.retainedPortSplitEquiv_geometryPair, P.retainedPortSplitEquiv_geometryPair]
  exact P.geometryOnRetainedSplit_involutive δ a k _

/-- On every retained interior port this is exactly the original square-corner pairing. -/
theorem retainedGeometryPair_interior (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (p : InteriorPort δ (P.domain δ)) :
    P.retainedGeometryPair δ a k (P.retainedPortOfInterior δ a k p) =
      P.retainedPortOfInterior δ a k p.cornerPair := by
  apply (P.retainedPortSplitEquiv δ a k).injective
  rw [P.retainedPortSplitEquiv_geometryPair]
  simp [geometryOnRetainedSplit]

/-- On every surviving actual exterior port this is exactly the truncated cyclic cap. -/
theorem retainedGeometryPair_boundaryCap (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (p : P.SurvivingBoundaryCapPort δ a k) :
    P.retainedGeometryPair δ a k (P.retainedPortOfBoundaryCap δ a k p) =
      P.retainedPortOfBoundaryCap δ a k (P.truncatedBoundaryCapPair δ a k p) := by
  apply (P.retainedPortSplitEquiv δ a k).injective
  rw [P.retainedPortSplitEquiv_geometryPair]
  simp [geometryOnRetainedSplit]

/-- The surviving actual endpoint occurrence preceding the chosen wired arc. -/
def wiredStartPort (δ : PositiveMesh) (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    P.RetainedPort δ a k :=
  (P.retainedPortSplitEquiv δ a k).symm
    (Sum.inr (P.survivingBoundaryCapEquiv δ a k (capStartTerminal a hk)))

/-- The surviving actual endpoint occurrence following the chosen wired arc. -/
def wiredFinishPort (δ : PositiveMesh) (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    P.RetainedPort δ a k :=
  (P.retainedPortSplitEquiv δ a k).symm
    (Sum.inr (P.survivingBoundaryCapEquiv δ a k (capFinishTerminal a hk)))

theorem wiredPorts_ne (δ : PositiveMesh) (a : ZMod (m + 3)) {k : ℕ}
    (hk : k ≤ m + 2) : P.wiredStartPort δ a hk ≠ P.wiredFinishPort δ a hk := by
  intro h
  apply P.survivingBoundaryCapTerminals_ne δ a hk
  exact Sum.inr.inj ((P.retainedPortSplitEquiv δ a k).symm.injective h)

/-- The start terminal is attached to the actual initial wired mark. -/
theorem wiredStartPort_primalVertex (δ : PositiveMesh) (a : ZMod (m + 3)) {k : ℕ}
    (hk : k ≤ m + 2) :
    (P.wiredStartPort δ a hk).val.toLatticePort.primalVertex = P.vertex a := by
  change (P.boundaryCapPort δ (capStartTerminal a hk).val).toLatticePort.primalVertex = _
  exact P.capStartTerminal_primalVertex δ a hk

/-- The finish terminal is attached to the actual final wired mark. -/
theorem wiredFinishPort_primalVertex (δ : PositiveMesh) (a : ZMod (m + 3)) {k : ℕ}
    (hk : k ≤ m + 2) :
    (P.wiredFinishPort δ a hk).val.toLatticePort.primalVertex = P.vertex (a + k) := by
  change (P.boundaryCapPort δ (capFinishTerminal a hk).val).toLatticePort.primalVertex = _
  exact P.capFinishTerminal_primalVertex δ a hk

/-- The exactly two fixed ports are derived from the geometric constituents. -/
theorem retainedGeometryPair_fixed_iff (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (p : P.RetainedPort δ a k) :
    P.retainedGeometryPair δ a k p = p ↔
      p = P.wiredStartPort δ a hk2 ∨ p = P.wiredFinishPort δ a hk2 := by
  rw [← (P.retainedPortSplitEquiv δ a k).injective.eq_iff,
    P.retainedPortSplitEquiv_geometryPair, P.geometryOnRetainedSplit_fixed_iff δ a hk1 hk2]
  simp only [wiredStartPort, wiredFinishPort, Equiv.eq_symm_apply]

/-- The actual geometric pairing bundled as its proved own inverse. -/
def retainedGeometryPairEquiv (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    Equiv.Perm (P.RetainedPort δ a k) where
  toFun := P.retainedGeometryPair δ a k
  invFun := P.retainedGeometryPair δ a k
  left_inv := P.retainedGeometryPair_involutive δ a k
  right_inv := P.retainedGeometryPair_involutive δ a k

@[simp] theorem retainedGeometryPairEquiv_apply (δ : PositiveMesh)
    (a : ZMod (m + 3)) (k : ℕ) (p : P.RetainedPort δ a k) :
    P.retainedGeometryPairEquiv δ a k p = P.retainedGeometryPair δ a k p := rfl

/-- The actual retained finite port graph. Configuration-local and geometric pairings
occupy separate layers, so coincident port pairs never lose their distinct edge identities. -/
def dobrushinPortGraph (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ))) :
    SimpleGraph (P.RetainedPort δ a k × Bool) :=
  pairingGraph (P.retainedLocalPairEquiv δ a k C) (P.retainedGeometryPairEquiv δ a k)
    (P.retainedLocalPair_involutive δ a k C) (P.retainedGeometryPair_involutive δ a k)

/-- Every actual configuration has exactly one simple finite port path oriented
from this wired arc's start to its finish. Other components may remain closed loops. -/
theorem dobrushinPortGraph_existsUnique_isPath (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ))) :
    ∃! p : (P.dobrushinPortGraph δ a k C).Walk
      (P.wiredStartPort δ a hk2, true) (P.wiredFinishPort δ a hk2, true), p.IsPath := by
  classical
  let : Finite (P.RetainedPort δ a k) := P.retainedPort_finite δ a k
  let : Fintype (P.RetainedPort δ a k) := Fintype.ofFinite _
  exact pairingGraph_existsUnique_isPath
    (P.retainedLocalPairEquiv δ a k C) (P.retainedGeometryPairEquiv δ a k)
    (P.retainedLocalPair_involutive δ a k C) (P.retainedGeometryPair_involutive δ a k)
    (P.retainedLocalPair_ne δ a k C) (P.wiredPorts_ne δ a hk2)
    (P.retainedGeometryPair_fixed_iff δ a hk1 hk2)

end
end PottsContinuity.FKC.LatticePolygon
