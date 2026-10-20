-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/InteriorCorners.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.DomainBonds
public import PottsContinuity.FKC.Domains.LatticeCells

/-!
# Corner pairing inside actual lattice cells

The closure of a genuine open cell is its closed coordinate square. In
particular all four of its unit sides lie in that closure. When the open cell
lies in a domain, the full-grid corner pairing therefore lands on another
actual domain bond. For lattice polygons the hypothesis is equivalent to
membership of the actual cell center in the derived Jordan interior.

Only ports facing interior cells are treated here. Boundary caps and the two
marked terminals are not constructed or assumed.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set

noncomputable section

/-- The full closure includes all four sides and all four vertices. -/
theorem closure_openLatticeCell (δ : PositiveMesh) (c : LatticeVertex) :
    closure (openLatticeCell δ c) =
      Complex.re ⁻¹' Icc (δ.val * (c.1 : ℝ)) (δ.val * ((c.1 : ℝ) + 1)) ∩
      Complex.im ⁻¹' Icc (δ.val * (c.2 : ℝ)) (δ.val * ((c.2 : ℝ) + 1)) := by
  have hx : δ.val * (c.1 : ℝ) ≠ δ.val * ((c.1 : ℝ) + 1) := by nlinarith [δ.property]
  have hy : δ.val * (c.2 : ℝ) ≠ δ.val * ((c.2 : ℝ) + 1) := by nlinarith [δ.property]
  change closure (Complex.equivRealProdCLM.toHomeomorph ⁻¹'
    (Ioo (δ.val * (c.1 : ℝ)) (δ.val * ((c.1 : ℝ) + 1)) ×ˢ
     Ioo (δ.val * (c.2 : ℝ)) (δ.val * ((c.2 : ℝ) + 1)))) = _
  rw [← Homeomorph.preimage_closure, closure_prod_eq, closure_Ioo hx, closure_Ioo hy]
  rfl

namespace Medial

/-- Every integer corner of a cell is in its actual Euclidean closure. -/
theorem latticeEmbed_mem_closure_openLatticeCell_of_corner (δ : PositiveMesh)
    {c v : LatticeVertex} (hv : IsUnitCellCorner c v) :
    latticeEmbed δ v ∈ closure (openLatticeCell δ c) := by
  rw [closure_openLatticeCell]
  rcases hv with ⟨hx | hx, hy | hy⟩ <;>
    simp only [mem_inter_iff, mem_preimage, mem_Icc, latticeEmbed] <;>
    simp only [hx, hy, Int.cast_add, Int.cast_one] <;>
    constructor <;> constructor <;> nlinarith [δ.property]

/-- The complete closed segment between any two corners lies in the cell closure. -/
theorem segment_subset_closure_openLatticeCell_of_corners (δ : PositiveMesh)
    {c u v : LatticeVertex} (hu : IsUnitCellCorner c u) (hv : IsUnitCellCorner c v) :
    segment ℝ (latticeEmbed δ u) (latticeEmbed δ v) ⊆ closure (openLatticeCell δ c) :=
  (convex_openLatticeCell δ c).closure.segment_subset
    (latticeEmbed_mem_closure_openLatticeCell_of_corner δ hu)
    (latticeEmbed_mem_closure_openLatticeCell_of_corner δ hv)

/-- Every one of the four cell-side bonds has its whole closed segment in the cell closure. -/
theorem port_segment_subset_closure_cell (δ : PositiveMesh) (p : LatticePort) :
    segment ℝ (latticeEmbed δ p.bond.source) (latticeEmbed δ p.bond.target) ⊆
      closure (openLatticeCell δ p.faceBase) :=
  segment_subset_closure_openLatticeCell_of_corners δ p.source_isUnitCellCorner
    p.target_isUnitCellCorner

/-- A cell contained in the domain supplies all its sides as actual domain bonds. -/
theorem port_segment_subset_closure_domain (δ : PositiveMesh) {D : Set ℂ}
    (p : LatticePort) (hp : openLatticeCell δ p.faceBase ⊆ D) :
    segment ℝ (latticeEmbed δ p.bond.source) (latticeEmbed δ p.bond.target) ⊆ closure D :=
  (port_segment_subset_closure_cell δ p).trans (closure_mono hp)

/-- The neighboring bond across an interior corner exists in the actual closure graph. -/
theorem cornerPair_segment_subset_closure_domain (δ : PositiveMesh) {D : Set ℂ}
    (p : LatticePort) (hp : openLatticeCell δ p.faceBase ⊆ D) :
    segment ℝ (latticeEmbed δ p.cornerPair.bond.source)
      (latticeEmbed δ p.cornerPair.bond.target) ⊆ closure D := by
  apply port_segment_subset_closure_domain δ p.cornerPair
  simpa only [LatticePort.cornerPair_faceBase] using hp

namespace DomainPort

variable {δ : PositiveMesh} {D : Set ℂ}

/-- The full-grid corner pairing, with its neighboring bond proved to belong to the domain. -/
def cornerPairOfInterior (p : DomainPort δ D)
    (hp : openLatticeCell δ p.toLatticePort.faceBase ⊆ D) : DomainPort δ D :=
  ⟨⟨p.toLatticePort.cornerPair.bond,
      cornerPair_segment_subset_closure_domain δ p.toLatticePort hp⟩,
    p.toLatticePort.cornerPair.tip, p.toLatticePort.cornerPair.side⟩

@[simp] theorem toLatticePort_cornerPairOfInterior (p : DomainPort δ D)
    (hp : openLatticeCell δ p.toLatticePort.faceBase ⊆ D) :
    (p.cornerPairOfInterior hp).toLatticePort = p.toLatticePort.cornerPair := rfl

end DomainPort

/-- Precisely the actual domain ports facing an entire interior open cell. -/
abbrev InteriorPort (δ : PositiveMesh) (D : Set ℂ) :=
  {p : DomainPort δ D // openLatticeCell δ p.toLatticePort.faceBase ⊆ D}

namespace InteriorPort

variable {δ : PositiveMesh} {D : Set ℂ}

def toLatticePort (p : InteriorPort δ D) : LatticePort := p.val.toLatticePort

theorem toLatticePort_injective : Function.Injective (@toLatticePort δ D) := by
  intro p q h
  exact Subtype.ext (DomainPort.toLatticePort_injective h)

/-- The actual domain-bond membership follows from the cell hypothesis. -/
def ofCell (p : LatticePort) (hp : openLatticeCell δ p.faceBase ⊆ D) :
    InteriorPort δ D :=
  ⟨⟨⟨p.bond, port_segment_subset_closure_domain δ p hp⟩, p.tip, p.side⟩, hp⟩

@[simp] theorem toLatticePort_ofCell (p : LatticePort)
    (hp : openLatticeCell δ p.faceBase ⊆ D) : (ofCell p hp).toLatticePort = p := rfl

theorem finite (δ : PositiveMesh) {D : Set ℂ} (hD : Bornology.IsBounded D) :
    Finite (InteriorPort δ D) := by
  let := DomainPort.finite δ hD
  infer_instance

/-- Cross to the other actual side of the same interior unit cell at the same corner. -/
def cornerPair (p : InteriorPort δ D) : InteriorPort δ D :=
  ⟨p.val.cornerPairOfInterior p.property, by
    change openLatticeCell δ p.val.toLatticePort.cornerPair.faceBase ⊆ D
    rw [LatticePort.cornerPair_faceBase]
    exact p.property⟩

@[simp] theorem toLatticePort_cornerPair (p : InteriorPort δ D) :
    p.cornerPair.toLatticePort = p.toLatticePort.cornerPair := rfl

theorem cornerPair_involutive : Function.Involutive (@cornerPair δ D) := by
  intro p
  apply toLatticePort_injective
  rw [toLatticePort_cornerPair, toLatticePort_cornerPair]
  exact LatticePort.cornerPair_involutive _

theorem cornerPair_ne (p : InteriorPort δ D) : p.cornerPair ≠ p := by
  intro h
  apply p.toLatticePort.cornerPair_ne
  simpa only [toLatticePort_cornerPair] using congrArg toLatticePort h

theorem cornerPair_faceBase (p : InteriorPort δ D) :
    p.cornerPair.toLatticePort.faceBase = p.toLatticePort.faceBase :=
  p.toLatticePort.cornerPair_faceBase

theorem cornerPair_primalVertex (p : InteriorPort δ D) :
    p.cornerPair.toLatticePort.primalVertex = p.toLatticePort.primalVertex :=
  p.toLatticePort.cornerPair_primalVertex

/-- For an actual lattice polygon, center membership proves the entire cell condition. -/
def ofCenter {m : ℕ} (P : LatticePolygon m) (δ : PositiveMesh)
    (p : LatticePort) (hp : latticeCellCenter δ p.faceBase ∈ P.domain δ) :
    InteriorPort δ (P.domain δ) :=
  ofCell p ((P.openLatticeCell_subset_domain_iff_center δ p.faceBase).mpr hp)

@[simp] theorem toLatticePort_ofCenter {m : ℕ} (P : LatticePolygon m) (δ : PositiveMesh)
    (p : LatticePort) (hp : latticeCellCenter δ p.faceBase ∈ P.domain δ) :
    (ofCenter P δ p hp).toLatticePort = p := rfl

end InteriorPort

end Medial
end
end PottsContinuity.FKC
