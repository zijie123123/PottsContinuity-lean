-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/BoundaryCaps.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.BoundaryCellSides
public import PottsContinuity.FKC.Medial.DomainBonds

/-!
# Actual exterior boundary ports and cyclic caps

Each original boundary edge has one actual exterior cell. Its two ports in
that cell are identified by the original cyclic endpoints, with a proved
conversion to the normalized bond's endpoint flag. These actual domain ports
are distinct. At each cyclic boundary vertex the preceding edge's final port
is paired with the following edge's initial port.

The pairing below acts on the range of these constructed actual ports. This
file does not assume that this range exhausts all exterior domain ports, nor
that the two ports joined by a cap have the same unit-cell base.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set Medial

noncomputable section

namespace Medial.LatticeBond

theorem endpoint_injective (e : LatticeBond) : Function.Injective e.endpoint := by
  intro t u h
  cases t <;> cases u <;> simp_all [endpoint, e.source_ne_target, e.source_ne_target.symm]

end Medial.LatticeBond

namespace LatticePolygon

variable {m : ℕ} (P : LatticePolygon m)

/-- Different original cyclic edges have different normalized actual bonds. -/
theorem boundaryBond_injective : Function.Injective P.boundaryBond := by
  intro i j h
  by_contra hij
  apply P.edge_ne hij
  rw [← P.boundaryBond_toSym2 i, ← P.boundaryBond_toSym2 j, h]

/-- The canonical boundary bond, with its full segment proved in the actual closure. -/
def boundaryDomainBond (δ : PositiveMesh) (i : ZMod (m + 3)) :
    DomainBond δ (P.domain δ) :=
  ⟨P.boundaryBond i, by
    rcases Sym2.eq_iff.mp (P.boundaryBond_toSym2 i) with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [hs, ht]
      exact (P.edge_subset_carrier δ i).trans (P.carrier_subset_closure_domain δ)
    · rw [hs, ht, segment_symm]
      exact (P.edge_subset_carrier δ i).trans (P.carrier_subset_closure_domain δ)⟩

@[simp] theorem boundaryDomainBond_val (δ : PositiveMesh) (i : ZMod (m + 3)) :
    (P.boundaryDomainBond δ i).val = P.boundaryBond i := rfl

/-- The uniquely proved exterior side of the actual boundary bond. -/
def boundaryOutsideSide (δ : PositiveMesh) (i : ZMod (m + 3)) : Bool :=
  Classical.choose (P.boundaryBond_existsUnique_outside_cell δ i)

theorem boundaryOutsideSide_spec (δ : PositiveMesh) (i : ZMod (m + 3)) :
    openLatticeCell δ ((P.boundaryBond i).faceBase (P.boundaryOutsideSide δ i)) ⊆
      P.exterior δ :=
  (Classical.choose_spec (P.boundaryBond_existsUnique_outside_cell δ i)).1

theorem eq_boundaryOutsideSide_iff (δ : PositiveMesh) (i : ZMod (m + 3)) (s : Bool) :
    s = P.boundaryOutsideSide δ i ↔
      openLatticeCell δ ((P.boundaryBond i).faceBase s) ⊆ P.exterior δ := by
  constructor
  · rintro rfl
    exact P.boundaryOutsideSide_spec δ i
  · exact (Classical.choose_spec (P.boundaryBond_existsUnique_outside_cell δ i)).2 s

/-- The original cyclic endpoint belonging to a boundary-edge endpoint occurrence. -/
def boundaryCapVertexIndex (r : ZMod (m + 3) × Bool) : ZMod (m + 3) :=
  if r.2 then r.1 + 1 else r.1

 theorem existsUnique_boundaryTip (i : ZMod (m + 3)) (b : Bool) :
    ∃! tip : Bool, (P.boundaryBond i).endpoint tip = P.vertex (boundaryCapVertexIndex (i, b)) := by
  have h : ∃ tip : Bool,
      (P.boundaryBond i).endpoint tip = P.vertex (boundaryCapVertexIndex (i, b)) := by
    cases b
    · rcases Sym2.eq_iff.mp (P.boundaryBond_toSym2 i) with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact ⟨false, hs⟩
      · exact ⟨true, ht⟩
    · rcases Sym2.eq_iff.mp (P.boundaryBond_toSym2 i) with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact ⟨true, ht⟩
      · exact ⟨false, hs⟩
  obtain ⟨tip, htip⟩ := h
  exact ⟨tip, htip, fun t ht => (P.boundaryBond i).endpoint_injective (ht.trans htip.symm)⟩

/-- Convert a cyclic start/end flag to the actual normalized bond endpoint flag. -/
def boundaryTip (i : ZMod (m + 3)) (b : Bool) : Bool :=
  Classical.choose (P.existsUnique_boundaryTip i b)

theorem boundaryTip_spec (i : ZMod (m + 3)) (b : Bool) :
    (P.boundaryBond i).endpoint (P.boundaryTip i b) =
      P.vertex (boundaryCapVertexIndex (i, b)) :=
  (Classical.choose_spec (P.existsUnique_boundaryTip i b)).1

/-- A genuine domain port at the specified original boundary-edge endpoint,
facing the unique actual exterior cell. -/
def boundaryCapPort (δ : PositiveMesh) (r : ZMod (m + 3) × Bool) :
    DomainPort δ (P.domain δ) :=
  ⟨P.boundaryDomainBond δ r.1, P.boundaryTip r.1 r.2, P.boundaryOutsideSide δ r.1⟩

@[simp] theorem boundaryCapPort_bond (δ : PositiveMesh) (r : ZMod (m + 3) × Bool) :
    (P.boundaryCapPort δ r).bond.val = P.boundaryBond r.1 := rfl

theorem boundaryCapPort_primalVertex (δ : PositiveMesh) (r : ZMod (m + 3) × Bool) :
    (P.boundaryCapPort δ r).toLatticePort.primalVertex =
      P.vertex (boundaryCapVertexIndex r) := P.boundaryTip_spec r.1 r.2

@[simp] theorem boundaryCapPort_start (δ : PositiveMesh) (i : ZMod (m + 3)) :
    (P.boundaryCapPort δ (i, false)).toLatticePort.primalVertex = P.vertex i :=
  P.boundaryCapPort_primalVertex δ (i, false)

@[simp] theorem boundaryCapPort_finish (δ : PositiveMesh) (i : ZMod (m + 3)) :
    (P.boundaryCapPort δ (i, true)).toLatticePort.primalVertex = P.vertex (i + 1) :=
  P.boundaryCapPort_primalVertex δ (i, true)

theorem boundaryCapPort_exterior (δ : PositiveMesh) (r : ZMod (m + 3) × Bool) :
    openLatticeCell δ (P.boundaryCapPort δ r).toLatticePort.faceBase ⊆ P.exterior δ :=
  P.boundaryOutsideSide_spec δ r.1

theorem boundaryCapPort_injective (δ : PositiveMesh) : Function.Injective (P.boundaryCapPort δ) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hij : i = j := P.boundaryBond_injective (congrArg (fun p => p.bond.val) h)
  subst j
  have hv := congrArg (fun p => p.toLatticePort.primalVertex) h
  rw [P.boundaryCapPort_primalVertex, P.boundaryCapPort_primalVertex] at hv
  cases b <;> cases c
  · rfl
  · exact ((P.adjacent i).ne (by simpa [boundaryCapVertexIndex] using hv)).elim
  · exact ((P.adjacent i).ne (by simpa [boundaryCapVertexIndex] using hv.symm)).elim
  · rfl

/-- Exact cyclic cap pairing of original boundary-edge endpoint occurrences. -/
def boundaryCapPartner (r : ZMod (m + 3) × Bool) : ZMod (m + 3) × Bool :=
  if r.2 then (r.1 + 1, false) else (r.1 - 1, true)

theorem boundaryCapPartner_involutive : Function.Involutive (boundaryCapPartner (m := m)) := by
  rintro ⟨i, b⟩
  cases b <;> simp [boundaryCapPartner]

theorem boundaryCapPartner_ne (r : ZMod (m + 3) × Bool) : boundaryCapPartner r ≠ r := by
  rcases r with ⟨i, b⟩
  cases b <;> simp [boundaryCapPartner]

theorem boundaryCapPartner_vertex (r : ZMod (m + 3) × Bool) :
    boundaryCapVertexIndex (boundaryCapPartner r) = boundaryCapVertexIndex r := by
  rcases r with ⟨i, b⟩
  cases b <;> simp [boundaryCapPartner, boundaryCapVertexIndex]

/-- Both actual cap ports are attached to exactly the same original boundary vertex. -/
theorem boundaryCapPort_partner_primalVertex (δ : PositiveMesh) (r : ZMod (m + 3) × Bool) :
    (P.boundaryCapPort δ (boundaryCapPartner r)).toLatticePort.primalVertex =
      (P.boundaryCapPort δ r).toLatticePort.primalVertex := by
  rw [P.boundaryCapPort_primalVertex, P.boundaryCapPort_primalVertex, boundaryCapPartner_vertex]

/-- The actual constructed exterior domain ports, without an exhaustion assertion. -/
abbrev BoundaryCapPort (δ : PositiveMesh) :=
  {p : DomainPort δ (P.domain δ) // p ∈ Set.range (P.boundaryCapPort δ)}

/-- No geometric identifications are made: cyclic occurrences biject with their actual ports. -/
def boundaryCapEquiv (δ : PositiveMesh) :
    (ZMod (m + 3) × Bool) ≃ P.BoundaryCapPort δ :=
  Equiv.ofInjective (P.boundaryCapPort δ) (P.boundaryCapPort_injective δ)

@[simp] theorem boundaryCapEquiv_val (δ : PositiveMesh) (r : ZMod (m + 3) × Bool) :
    (P.boundaryCapEquiv δ r).val = P.boundaryCapPort δ r := rfl

/-- The outside cap pairing on the actual constructed domain ports. -/
def boundaryCapPair (δ : PositiveMesh) (p : P.BoundaryCapPort δ) : P.BoundaryCapPort δ :=
  P.boundaryCapEquiv δ (boundaryCapPartner ((P.boundaryCapEquiv δ).symm p))

@[simp] theorem boundaryCapPair_equiv (δ : PositiveMesh) (r : ZMod (m + 3) × Bool) :
    P.boundaryCapPair δ (P.boundaryCapEquiv δ r) =
      P.boundaryCapEquiv δ (boundaryCapPartner r) := by
  simp [boundaryCapPair]

end LatticePolygon
end

end PottsContinuity.FKC
