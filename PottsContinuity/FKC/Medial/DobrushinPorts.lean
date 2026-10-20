-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/DobrushinPorts.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.BoundaryPairing
public import PottsContinuity.FKC.Medial.TruncatedCaps

/-!
# Actual ports retained after removing a wired arc's exterior occurrences

All interior-facing ports are retained, including those on removed boundary
edges. An exterior-facing port is retained exactly when its original edge is
not removed. The actual FK drawing opens every removed edge; its local pairing
therefore restricts to a fixed-point-free involution of precisely this carrier.

The selected arc is an arbitrary cyclic forward arc. Its orientation is not
asserted to be counterclockwise, and this module does not assume or assert the
existence of the final two-terminal interface.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set Medial

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

/-- Delete exactly the exterior-facing occurrences of removed original edges. -/
abbrev RetainedPort (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :=
  {p : DomainPort δ (P.domain δ) //
    openLatticeCell δ p.toLatticePort.faceBase ⊆ P.domain δ ∨
      p.bond.toGraphEdge ∉ P.forwardArcRemovedEdges δ a k}

/-- Finiteness follows from the actual bounded polygon domain. -/
instance retainedPort_finite (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    Finite (P.RetainedPort δ a k) := by
  let := DomainPort.finite δ (P.isJordanDomain δ).isBounded
  infer_instance

/-- Every actual interior-facing port remains present. -/
def retainedPortOfInterior (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (p : InteriorPort δ (P.domain δ)) : P.RetainedPort δ a k :=
  ⟨p.val, Or.inl p.property⟩

/-- Every surviving actual exterior cap port remains present. -/
def retainedPortOfBoundaryCap (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (p : P.SurvivingBoundaryCapPort δ a k) : P.RetainedPort δ a k :=
  ⟨p.val.val, Or.inr p.property⟩

@[simp] theorem retainedPortOfInterior_val (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (p : InteriorPort δ (P.domain δ)) :
    (P.retainedPortOfInterior δ a k p).val = p.val := rfl

@[simp] theorem retainedPortOfBoundaryCap_val (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (p : P.SurvivingBoundaryCapPort δ a k) :
    (P.retainedPortOfBoundaryCap δ a k p).val = p.val.val := rfl

/-- The retained carrier consists exactly of all interior ports and the surviving
actual exterior caps; the original port and both flags are preserved. -/
def retainedPortSplitEquiv (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    P.RetainedPort δ a k ≃
      InteriorPort δ (P.domain δ) ⊕ P.SurvivingBoundaryCapPort δ a k := by
  classical
  exact
    { toFun := fun p => if h : openLatticeCell δ p.val.toLatticePort.faceBase ⊆ P.domain δ
        then Sum.inl ⟨p.val, h⟩
        else Sum.inr ⟨⟨p.val, (P.domainPort_not_inside_iff_mem_boundaryCap δ p.val).mp h⟩,
          p.property.resolve_left h⟩
      invFun := Sum.elim (P.retainedPortOfInterior δ a k) (P.retainedPortOfBoundaryCap δ a k)
      left_inv := by intro p; dsimp only; split_ifs <;> rfl
      right_inv := by
        rintro (p | p)
        · simp [retainedPortOfInterior, p.property]
        · have hp := (P.domainPort_not_inside_iff_mem_boundaryCap δ p.val.val).mpr p.val.property
          simp [retainedPortOfBoundaryCap, hp] }

@[simp] theorem retainedPortSplitEquiv_interior (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (p : InteriorPort δ (P.domain δ)) :
    P.retainedPortSplitEquiv δ a k (P.retainedPortOfInterior δ a k p) = Sum.inl p := by
  simp [retainedPortSplitEquiv, retainedPortOfInterior, p.property]

@[simp] theorem retainedPortSplitEquiv_boundaryCap (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (p : P.SurvivingBoundaryCapPort δ a k) :
    P.retainedPortSplitEquiv δ a k (P.retainedPortOfBoundaryCap δ a k p) = Sum.inr p := by
  have hp := (P.domainPort_not_inside_iff_mem_boundaryCap δ p.val.val).mpr p.val.property
  simp [retainedPortSplitEquiv, retainedPortOfBoundaryCap, hp]

@[simp] theorem retainedPortSplitEquiv_symm_inl (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (p : InteriorPort δ (P.domain δ)) :
    (P.retainedPortSplitEquiv δ a k).symm (Sum.inl p) =
      P.retainedPortOfInterior δ a k p := rfl

@[simp] theorem retainedPortSplitEquiv_symm_inr (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (p : P.SurvivingBoundaryCapPort δ a k) :
    (P.retainedPortSplitEquiv δ a k).symm (Sum.inr p) =
      P.retainedPortOfBoundaryCap δ a k p := rfl

/-- Opening all removed edges preserves retained occurrences: at a removed edge
the open pairing stays on the same cell side; otherwise its original edge is unchanged. -/
theorem localPair_drawing_retained (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ)))
    (p : P.RetainedPort δ a k) :
    openLatticeCell δ
        (DomainPort.localPair (C ∪ P.forwardArcRemovedEdges δ a k) p.val).toLatticePort.faceBase
        ⊆ P.domain δ ∨
      (DomainPort.localPair (C ∪ P.forwardArcRemovedEdges δ a k) p.val).bond.toGraphEdge
        ∉ P.forwardArcRemovedEdges δ a k := by
  classical
  by_cases hR : p.val.bond.toGraphEdge ∈ P.forwardArcRemovedEdges δ a k
  · left
    rw [DomainPort.localPair_faceBase_of_open _ _ (Finset.mem_union.mpr (Or.inr hR))]
    exact p.property.resolve_right (not_not.mpr hR)
  · right
    simpa only [DomainPort.localPair_bond] using hR

/-- The actual local drawing pairing restricted to the exact retained carrier. -/
def retainedLocalPair (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ)))
    (p : P.RetainedPort δ a k) : P.RetainedPort δ a k :=
  ⟨DomainPort.localPair (C ∪ P.forwardArcRemovedEdges δ a k) p.val,
    P.localPair_drawing_retained δ a k C p⟩

@[simp] theorem retainedLocalPair_val (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ)))
    (p : P.RetainedPort δ a k) :
    (P.retainedLocalPair δ a k C p).val =
      DomainPort.localPair (C ∪ P.forwardArcRemovedEdges δ a k) p.val := rfl

theorem retainedLocalPair_involutive (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ))) :
    Function.Involutive (P.retainedLocalPair δ a k C) := by
  intro p
  apply Subtype.ext
  exact DomainPort.localPair_involutive (C ∪ P.forwardArcRemovedEdges δ a k) p.val

theorem retainedLocalPair_ne (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ)))
    (p : P.RetainedPort δ a k) : P.retainedLocalPair δ a k C p ≠ p := by
  intro h
  exact DomainPort.localPair_ne (C ∪ P.forwardArcRemovedEdges δ a k) p.val
    (congrArg Subtype.val h)

@[simp] theorem retainedLocalPair_bond (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ)))
    (p : P.RetainedPort δ a k) :
    (P.retainedLocalPair δ a k C p).val.bond = p.val.bond :=
  DomainPort.localPair_bond _ _

@[simp] theorem retainedLocalPair_position (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ)))
    (p : P.RetainedPort δ a k) :
    (P.retainedLocalPair δ a k C p).val.toLatticePort.position δ =
      p.val.toLatticePort.position δ := DomainPort.localPair_position _ _

/-- A genuine permutation; both inverse identities follow from the proved restriction. -/
def retainedLocalPairEquiv (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ))) :
    Equiv.Perm (P.RetainedPort δ a k) where
  toFun := P.retainedLocalPair δ a k C
  invFun := P.retainedLocalPair δ a k C
  left_inv := P.retainedLocalPair_involutive δ a k C
  right_inv := P.retainedLocalPair_involutive δ a k C

@[simp] theorem retainedLocalPairEquiv_apply (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (C : FiniteFK.Configuration (domainLatticeGraph δ (P.domain δ)))
    (p : P.RetainedPort δ a k) :
    P.retainedLocalPairEquiv δ a k C p = P.retainedLocalPair δ a k C p := rfl

end

end PottsContinuity.FKC.LatticePolygon
