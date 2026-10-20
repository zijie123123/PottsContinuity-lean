-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/BoundaryPairing.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.BoundaryCaps
public import PottsContinuity.FKC.Medial.DomainBondSides

/-!
# The complete geometric pairing on actual domain ports

Every exterior-facing actual domain port is one of the constructed cyclic
boundary ports. The original domain ports therefore split exhaustively and
disjointly into interior-cell ports and actual exterior cap ports. On the
first part the geometric matching is the genuine same-cell corner matching;
on the second it is the cyclic exterior cap matching.

This complete matching is a fixed-point-free involution preserving the actual
primal vertex. No wired arc is removed and no two-terminal condition is
introduced in this file.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set Medial

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

/-- Both normalized endpoint flags occur among the original cyclic start/end flags. -/
theorem boundaryTip_surjective (i : ZMod (m + 3)) : Function.Surjective (P.boundaryTip i) := by
  intro tip
  have h : (P.boundaryBond i).endpoint tip ∈ (P.boundaryBond i).toSym2 := by
    cases tip <;> simp [LatticeBond.endpoint, LatticeBond.toSym2]
  rw [P.boundaryBond_toSym2, Sym2.mem_iff] at h
  rcases h with h | h
  · refine ⟨false, (P.boundaryBond i).endpoint_injective ?_⟩
    exact (P.boundaryTip_spec i false).trans h.symm
  · refine ⟨true, (P.boundaryBond i).endpoint_injective ?_⟩
    exact (P.boundaryTip_spec i true).trans h.symm

/-- The actual cyclic cap ports exhaust exactly all exterior-facing domain ports. -/
theorem domainPort_exterior_iff_mem_boundaryCap (δ : PositiveMesh)
    (p : DomainPort δ (P.domain δ)) :
    openLatticeCell δ p.toLatticePort.faceBase ⊆ P.exterior δ ↔
      p ∈ Set.range (P.boundaryCapPort δ) := by
  constructor
  · intro hp
    change openLatticeCell δ (p.bond.val.faceBase p.side) ⊆ P.exterior δ at hp
    obtain ⟨i, hi⟩ := P.domainBond_boundary_of_outside_cell δ p.bond p.side hp
    have hs : p.side = P.boundaryOutsideSide δ i :=
      (P.eq_boundaryOutsideSide_iff δ i p.side).mpr (by simpa only [hi] using hp)
    obtain ⟨b, hb⟩ := P.boundaryTip_surjective i p.tip
    refine ⟨(i, b), DomainPort.toLatticePort_injective ?_⟩
    change (⟨P.boundaryBond i, P.boundaryTip i b, P.boundaryOutsideSide δ i⟩ : LatticePort) =
      ⟨p.bond.val, p.tip, p.side⟩
    rw [hb, hi, hs]
  · rintro ⟨r, rfl⟩
    exact P.boundaryCapPort_exterior δ r

theorem domainPort_not_inside_iff_exterior (δ : PositiveMesh)
    (p : DomainPort δ (P.domain δ)) :
    ¬(openLatticeCell δ p.toLatticePort.faceBase ⊆ P.domain δ) ↔
      openLatticeCell δ p.toLatticePort.faceBase ⊆ P.exterior δ := by
  constructor
  · intro hp
    exact (P.openLatticeCell_subset_domain_or_exterior δ p.toLatticePort.faceBase).resolve_left hp
  · intro ho hi
    exact Set.disjoint_left.mp (P.disjoint_domain_exterior δ)
      (hi (latticeCellCenter_mem δ _)) (ho (latticeCellCenter_mem δ _))

/-- The exterior cap range is exactly the complement of the actual interior port predicate. -/
theorem domainPort_not_inside_iff_mem_boundaryCap (δ : PositiveMesh)
    (p : DomainPort δ (P.domain δ)) :
    ¬(openLatticeCell δ p.toLatticePort.faceBase ⊆ P.domain δ) ↔
      p ∈ Set.range (P.boundaryCapPort δ) :=
  (P.domainPort_not_inside_iff_exterior δ p).trans
    (P.domainPort_exterior_iff_mem_boundaryCap δ p)

/-- The original port carrier is partitioned without discarding or adding any port. -/
def domainPortSplitEquiv (δ : PositiveMesh) :
    DomainPort δ (P.domain δ) ≃ InteriorPort δ (P.domain δ) ⊕ P.BoundaryCapPort δ := by
  classical
  exact
    { toFun := fun p => if h : openLatticeCell δ p.toLatticePort.faceBase ⊆ P.domain δ
        then Sum.inl ⟨p, h⟩
        else Sum.inr ⟨p, (P.domainPort_not_inside_iff_mem_boundaryCap δ p).mp h⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := by intro p; dsimp only; split_ifs <;> rfl
      right_inv := by
        rintro (p | p)
        · simp [p.property]
        · have hp := (P.domainPort_not_inside_iff_mem_boundaryCap δ p.val).mpr p.property
          simp [hp] }

@[simp] theorem domainPortSplitEquiv_interior (δ : PositiveMesh)
    (p : InteriorPort δ (P.domain δ)) : P.domainPortSplitEquiv δ p.val = Sum.inl p := by
  simp [domainPortSplitEquiv, p.property]

@[simp] theorem domainPortSplitEquiv_boundaryCap (δ : PositiveMesh)
    (p : P.BoundaryCapPort δ) : P.domainPortSplitEquiv δ p.val = Sum.inr p := by
  have hp := (P.domainPort_not_inside_iff_mem_boundaryCap δ p.val).mpr p.property
  simp [domainPortSplitEquiv, hp]

/-- The complete actual geometric matching: interior square corner or exterior cyclic cap. -/
def geometryPair (δ : PositiveMesh) (p : DomainPort δ (P.domain δ)) :
    DomainPort δ (P.domain δ) := by
  classical
  exact if h : openLatticeCell δ p.toLatticePort.faceBase ⊆ P.domain δ
    then (InteriorPort.cornerPair ⟨p, h⟩).val
    else (P.boundaryCapPair δ
      ⟨p, (P.domainPort_not_inside_iff_mem_boundaryCap δ p).mp h⟩).val

@[simp] theorem geometryPair_interior (δ : PositiveMesh)
    (p : InteriorPort δ (P.domain δ)) : P.geometryPair δ p.val = p.cornerPair.val := by
  simp [geometryPair, p.property]

@[simp] theorem geometryPair_boundaryCap (δ : PositiveMesh)
    (p : P.BoundaryCapPort δ) : P.geometryPair δ p.val = (P.boundaryCapPair δ p).val := by
  have hp := (P.domainPort_not_inside_iff_mem_boundaryCap δ p.val).mpr p.property
  simp [geometryPair, hp]

end

end PottsContinuity.FKC.LatticePolygon
