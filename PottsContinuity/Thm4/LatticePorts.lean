/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/LatticePorts.lean`.
Adaptation: namespace relocation; reuse PD lattice/embedding; coordinate adjacency via PD API.
Embedding injectivity copied from FKconvergence/LatticeEmbedding.lean.
-/
module

public import PottsContinuity.PD.Duality.LatticeEmbedding
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Actual square-lattice bonds and medial ports

A bond is a horizontal or vertical unit lattice segment, normalized by its
left or lower endpoint. A medial port records a bond, one of its two primal
endpoints, and one of its two adjacent unit cells. Thus four distinct port
identities project to each medial midpoint; later traversals must retain these
identities and their order rather than identify visits by their position.

The open local pairing stays in one dual cell and swaps primal endpoints.
The closed local pairing stays at one primal endpoint and swaps adjacent cells.
The corner pairing crosses the medial edge joining consecutive sides of one
actual unit cell. All coordinate and pairing identities are proved below on
the full integer lattice. No finite-domain boundary completion, two-terminal
condition, or strand existence is assumed or asserted here.
-/

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open PottsContinuity.PD.FK

private theorem latticeEmbed_injective (δ : PositiveMesh) :
    Function.Injective (latticeEmbed δ) := by
  intro u v h
  apply Prod.ext
  · have hre := congrArg Complex.re h
    have hcoord : (u.1 : ℝ) = (v.1 : ℝ) := mul_left_cancel₀ δ.property.ne' hre
    exact_mod_cast hcoord
  · have him := congrArg Complex.im h
    have hcoord : (u.2 : ℝ) = (v.2 : ℝ) := mul_left_cancel₀ δ.property.ne' him
    exact_mod_cast hcoord

/-- The two axes of a normalized unit lattice bond. -/
inductive LatticeAxis
  | horizontal
  | vertical
  deriving DecidableEq

instance : Fintype LatticeAxis where
  elems := {.horizontal, .vertical}
  complete := by intro a; cases a <;> simp

/-- A unit bond, based at its left endpoint if horizontal or lower endpoint if vertical. -/
structure LatticeBond where
  base : LatticeVertex
  axis : LatticeAxis
  deriving DecidableEq

namespace LatticeBond

open LatticeAxis

def source (e : LatticeBond) : LatticeVertex := e.base

def target (e : LatticeBond) : LatticeVertex :=
  match e.axis with
  | horizontal => (e.base.1 + 1, e.base.2)
  | vertical => (e.base.1, e.base.2 + 1)

theorem adjacent (e : LatticeBond) : PottsContinuity.PD.FK.squareLattice.Adj e.source e.target := by
  rcases e with ⟨⟨x, y⟩, ax⟩
  cases ax <;> simp [source, target, PottsContinuity.PD.FK.squareLattice_adj_iff]

theorem source_ne_target (e : LatticeBond) : e.source ≠ e.target := e.adjacent.ne

/-- The actual unoriented edge of the original square lattice. -/
def toSym2 (e : LatticeBond) : Sym2 LatticeVertex := s(e.source, e.target)

theorem toSym2_mem_edgeSet (e : LatticeBond) : e.toSym2 ∈ PottsContinuity.PD.FK.squareLattice.edgeSet :=
  PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr e.adjacent

theorem toSym2_injective : Function.Injective toSym2 := by
  rintro ⟨⟨x, y⟩, ax⟩ ⟨⟨z, w⟩, az⟩ h
  cases ax <;> cases az <;>
    simp only [toSym2, source, target, Sym2.eq_iff, Prod.mk.injEq] at h
  all_goals rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp_all <;> omega

/-- Every actual nearest-neighbor edge has a normalized bond representative. -/
theorem exists_of_adj {u v : LatticeVertex} (h : PottsContinuity.PD.FK.squareLattice.Adj u v) :
    ∃ e : LatticeBond, e.toSym2 = s(u, v) := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  simp only [PottsContinuity.PD.FK.squareLattice_adj_iff] at h
  rcases h with ⟨h | h, rfl⟩ | ⟨rfl, h | h⟩
  · subst z
    exact ⟨⟨(x, y), horizontal⟩, rfl⟩
  · subst x
    exact ⟨⟨(z, y), horizontal⟩, Sym2.eq_swap⟩
  · subst w
    exact ⟨⟨(x, y), vertical⟩, rfl⟩
  · subst y
    exact ⟨⟨(x, w), vertical⟩, Sym2.eq_swap⟩

/-- Normalization neither duplicates nor omits an original unit edge. -/
theorem existsUnique_of_adj {u v : LatticeVertex} (h : PottsContinuity.PD.FK.squareLattice.Adj u v) :
    ∃! e : LatticeBond, e.toSym2 = s(u, v) := by
  obtain ⟨e, he⟩ := exists_of_adj h
  exact ⟨e, he, fun f hf => toSym2_injective (hf.trans he.symm)⟩

/-- `false` is the normalized source, `true` is the target. -/
def endpoint (e : LatticeBond) (tip : Bool) : LatticeVertex :=
  if tip then e.target else e.source

/-- Lower-left corner of an adjacent unit cell. For horizontal bonds `false`
means below and `true` above; for vertical bonds `false` means left and `true` right. -/
def faceBase (e : LatticeBond) (side : Bool) : LatticeVertex :=
  match e.axis, side with
  | horizontal, false => (e.base.1, e.base.2 - 1)
  | horizontal, true => e.base
  | vertical, false => (e.base.1 - 1, e.base.2)
  | vertical, true => e.base

/-- The geometric medial vertex in the positive-mesh complex embedding. -/
noncomputable def midpoint (e : LatticeBond) (δ : PositiveMesh) : ℂ :=
  (latticeEmbed δ e.source + latticeEmbed δ e.target) / 2

end LatticeBond

/-- The four corners of the genuine unit square with lower-left corner `c`. -/
def IsUnitCellCorner (c v : LatticeVertex) : Prop :=
  (v.1 = c.1 ∨ v.1 = c.1 + 1) ∧ (v.2 = c.2 ∨ v.2 = c.2 + 1)

/-- A medial half-edge at a unit bond midpoint, distinguished by its primal
endpoint and adjacent unit cell. Distinct ports are not identified geometrically. -/
structure LatticePort where
  bond : LatticeBond
  tip : Bool
  side : Bool
  deriving DecidableEq

namespace LatticePort

open LatticeAxis

def primalVertex (p : LatticePort) : LatticeVertex := p.bond.endpoint p.tip

def faceBase (p : LatticePort) : LatticeVertex := p.bond.faceBase p.side

noncomputable def position (p : LatticePort) (δ : PositiveMesh) : ℂ := p.bond.midpoint δ

/-- At an open primal edge, turn around a dual cell. -/
def openPair (p : LatticePort) : LatticePort := ⟨p.bond, !p.tip, p.side⟩

/-- At a closed primal edge, turn around a primal endpoint. -/
def closedPair (p : LatticePort) : LatticePort := ⟨p.bond, p.tip, !p.side⟩

theorem openPair_involutive : Function.Involutive openPair := by
  rintro ⟨e, t, s⟩
  simp [openPair]

theorem closedPair_involutive : Function.Involutive closedPair := by
  rintro ⟨e, t, s⟩
  simp [closedPair]

theorem openPair_ne (p : LatticePort) : p.openPair ≠ p := by
  rcases p with ⟨e, t, s⟩
  cases t <;> simp [openPair]

theorem closedPair_ne (p : LatticePort) : p.closedPair ≠ p := by
  rcases p with ⟨e, t, s⟩
  cases s <;> simp [closedPair]

@[simp] theorem openPair_bond (p : LatticePort) : p.openPair.bond = p.bond := rfl
@[simp] theorem closedPair_bond (p : LatticePort) : p.closedPair.bond = p.bond := rfl
@[simp] theorem openPair_faceBase (p : LatticePort) : p.openPair.faceBase = p.faceBase := rfl
@[simp] theorem closedPair_primalVertex (p : LatticePort) :
    p.closedPair.primalVertex = p.primalVertex := rfl

theorem closedPair_faceBase_ne (p : LatticePort) :
    p.closedPair.faceBase ≠ p.faceBase := by
  rcases p with ⟨⟨⟨x, y⟩, ax⟩, t, s⟩
  cases ax <;> cases s <;>
    simp [closedPair, faceBase, LatticeBond.faceBase] <;> omega

@[simp] theorem openPair_position (p : LatticePort) (δ : PositiveMesh) :
    p.openPair.position δ = p.position δ := rfl

@[simp] theorem closedPair_position (p : LatticePort) (δ : PositiveMesh) :
    p.closedPair.position δ = p.position δ := rfl

/-- The actual local pairing selected by a primal bond's open/closed state. -/
def localPair (ω : LatticeBond → Bool) (p : LatticePort) : LatticePort :=
  if ω p.bond then p.openPair else p.closedPair

@[simp] theorem localPair_bond (ω : LatticeBond → Bool) (p : LatticePort) :
    (localPair ω p).bond = p.bond := by
  cases h : ω p.bond <;> simp [localPair, h]

theorem localPair_involutive (ω : LatticeBond → Bool) :
    Function.Involutive (localPair ω) := by
  intro p
  cases h : ω p.bond
  · simpa [localPair, h] using closedPair_involutive p
  · simpa [localPair, h] using openPair_involutive p

theorem localPair_ne (ω : LatticeBond → Bool) (p : LatticePort) : localPair ω p ≠ p := by
  cases h : ω p.bond <;> simp [localPair, h, openPair_ne, closedPair_ne]

@[simp] theorem localPair_position (ω : LatticeBond → Bool) (p : LatticePort)
    (δ : PositiveMesh) : (localPair ω p).position δ = p.position δ := by
  cases h : ω p.bond <;> simp [localPair, h]

/-- The endpoint of a port really is a corner of its adjacent unit cell. -/
theorem primalVertex_isUnitCellCorner (p : LatticePort) :
    IsUnitCellCorner p.faceBase p.primalVertex := by
  rcases p with ⟨⟨⟨x, y⟩, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;>
    simp [IsUnitCellCorner, primalVertex, faceBase, LatticeBond.endpoint,
      LatticeBond.source, LatticeBond.target, LatticeBond.faceBase]

theorem source_isUnitCellCorner (p : LatticePort) :
    IsUnitCellCorner p.faceBase p.bond.source :=
  primalVertex_isUnitCellCorner ⟨p.bond, false, p.side⟩

theorem target_isUnitCellCorner (p : LatticePort) :
    IsUnitCellCorner p.faceBase p.bond.target :=
  primalVertex_isUnitCellCorner ⟨p.bond, true, p.side⟩

/-- Cross the medial edge at the indicated corner to the other side of the
same unit square. The eight formulas use actual integer lattice coordinates. -/
def cornerPair (p : LatticePort) : LatticePort :=
  match p.bond.axis, p.tip, p.side with
  | horizontal, false, false => ⟨⟨(p.bond.base.1, p.bond.base.2 - 1), vertical⟩, true, true⟩
  | horizontal, false, true => ⟨⟨p.bond.base, vertical⟩, false, true⟩
  | horizontal, true, false => ⟨⟨(p.bond.base.1 + 1, p.bond.base.2 - 1), vertical⟩, true, false⟩
  | horizontal, true, true => ⟨⟨(p.bond.base.1 + 1, p.bond.base.2), vertical⟩, false, false⟩
  | vertical, false, false => ⟨⟨(p.bond.base.1 - 1, p.bond.base.2), horizontal⟩, true, true⟩
  | vertical, false, true => ⟨⟨p.bond.base, horizontal⟩, false, true⟩
  | vertical, true, false => ⟨⟨(p.bond.base.1 - 1, p.bond.base.2 + 1), horizontal⟩, true, false⟩
  | vertical, true, true => ⟨⟨(p.bond.base.1, p.bond.base.2 + 1), horizontal⟩, false, false⟩

theorem cornerPair_involutive : Function.Involutive cornerPair := by
  rintro ⟨⟨⟨x, y⟩, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;> simp [cornerPair]

theorem cornerPair_axis_ne (p : LatticePort) : p.cornerPair.bond.axis ≠ p.bond.axis := by
  rcases p with ⟨⟨⟨x, y⟩, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;> simp [cornerPair]

theorem cornerPair_ne (p : LatticePort) : p.cornerPair ≠ p := fun h =>
  p.cornerPair_axis_ne (congrArg (fun q => q.bond.axis) h)

/-- Crossing a medial edge stays at exactly the same primal square corner. -/
theorem cornerPair_primalVertex (p : LatticePort) :
    p.cornerPair.primalVertex = p.primalVertex := by
  rcases p with ⟨⟨⟨x, y⟩, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;>
    simp [cornerPair, primalVertex, LatticeBond.endpoint, LatticeBond.source, LatticeBond.target]

/-- Crossing a medial edge stays in exactly the same genuine unit square. -/
theorem cornerPair_faceBase (p : LatticePort) : p.cornerPair.faceBase = p.faceBase := by
  rcases p with ⟨⟨⟨x, y⟩, ax⟩, t, s⟩
  cases ax <;> cases t <;> cases s <;>
    simp [cornerPair, faceBase, LatticeBond.faceBase]

end LatticePort

end PottsContinuity.Thm4.Medial
