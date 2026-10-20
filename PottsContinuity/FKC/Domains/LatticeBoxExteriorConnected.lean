-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticeBoxExteriorConnected.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.FKC.Domains

open PottsContinuity.FKC
open SimpleGraph

def latticeBoxExteriorGraph (r : ℕ) : SimpleGraph {v : LatticeVertex // v ∉ latticeBox (0, 0) r} :=
  squareLattice.induce {v | v ∉ latticeBox (0, 0) r}

private theorem mem_exterior_of_x_lt (r : ℕ) (x y : ℤ) (h : x < -(r : ℤ)) :
    (x, y) ∉ latticeBox (0, 0) r := by
  rw [mem_latticeBox]
  omega

private theorem mem_exterior_of_x_gt (r : ℕ) (x y : ℤ) (h : (r : ℤ) < x) :
    (x, y) ∉ latticeBox (0, 0) r := by
  rw [mem_latticeBox]
  omega

private theorem mem_exterior_of_y_lt (r : ℕ) (x y : ℤ) (h : y < -(r : ℤ)) :
    (x, y) ∉ latticeBox (0, 0) r := by
  rw [mem_latticeBox]
  omega

private theorem mem_exterior_of_y_gt (r : ℕ) (x y : ℤ) (h : (r : ℤ) < y) :
    (x, y) ∉ latticeBox (0, 0) r := by
  rw [mem_latticeBox]
  omega

def xExteriorVertex (r : ℕ) (x y : ℤ)
    (hx : x < -(r : ℤ) ∨ (r : ℤ) < x) :
    {v : LatticeVertex // v ∉ latticeBox (0, 0) r} :=
  ⟨(x,y), by
    rcases hx with h | h
    · exact mem_exterior_of_x_lt r x y h
    · exact mem_exterior_of_x_gt r x y h⟩

def yExteriorVertex (r : ℕ) (x y : ℤ)
    (hy : y < -(r : ℤ) ∨ (r : ℤ) < y) :
    {v : LatticeVertex // v ∉ latticeBox (0, 0) r} :=
  ⟨(x,y), by
    rcases hy with h | h
    · exact mem_exterior_of_y_lt r x y h
    · exact mem_exterior_of_y_gt r x y h⟩

def verticalUpExteriorWalk (r : ℕ) (x y : ℤ)
    (hx : x < -(r : ℤ) ∨ (r : ℤ) < x) :
    ∀ n : ℕ, (latticeBoxExteriorGraph r).Walk
      (xExteriorVertex r x y hx)
      (xExteriorVertex r x (y + (n : ℤ)) hx) := by
  intro n
  induction n with
  | zero => simpa using (Walk.nil : (latticeBoxExteriorGraph r).Walk
      (xExteriorVertex r x y hx) (xExteriorVertex r x y hx))
  | succ n ih =>
      have hstep : squareLattice.Adj (x, y + (n : ℤ))
          (x, y + (n : ℤ) + 1) := by
        simp [squareLattice]
      have hstep' : (latticeBoxExteriorGraph r).Adj
          (xExteriorVertex r x (y+(n:ℤ)) hx)
          (xExteriorVertex r x (y+(n:ℤ)+1) hx) := hstep
      simpa only [Nat.cast_succ, add_assoc] using
        (ih.append (Walk.cons hstep' Walk.nil))

def horizontalRightExteriorWalk (r : ℕ) (x y : ℤ)
    (hy : y < -(r : ℤ) ∨ (r : ℤ) < y) :
    ∀ n : ℕ, (latticeBoxExteriorGraph r).Walk
      (yExteriorVertex r x y hy)
      (yExteriorVertex r (x + (n : ℤ)) y hy) := by
  intro n
  induction n with
  | zero => simpa using (Walk.nil : (latticeBoxExteriorGraph r).Walk
      (yExteriorVertex r x y hy) (yExteriorVertex r x y hy))
  | succ n ih =>
      have hstep : squareLattice.Adj (x + (n : ℤ), y)
          (x + (n : ℤ) + 1, y) := by
        simp [squareLattice]
      have hstep' : (latticeBoxExteriorGraph r).Adj
          (yExteriorVertex r (x+(n:ℤ)) y hy)
          (yExteriorVertex r (x+(n:ℤ)+1) y hy) := hstep
      simpa only [Nat.cast_succ, add_assoc] using
        (ih.append (Walk.cons hstep' Walk.nil))

def horizontalLeftExteriorWalk (r : ℕ) (x y : ℤ)
    (hy : y < -(r : ℤ) ∨ (r : ℤ) < y) (n : ℕ) :
    (latticeBoxExteriorGraph r).Walk
      (yExteriorVertex r x y hy)
      (yExteriorVertex r (x - (n : ℤ)) y hy) := by
  simpa using
    (horizontalRightExteriorWalk r (x - (n : ℤ)) y hy n).reverse

def verticalDownExteriorWalk (r : ℕ) (x y : ℤ)
    (hx : x < -(r : ℤ) ∨ (r : ℤ) < x) (n : ℕ) :
    (latticeBoxExteriorGraph r).Walk
      (xExteriorVertex r x y hx)
      (xExteriorVertex r x (y - (n : ℤ)) hx) := by
  simpa using (verticalUpExteriorWalk r x (y - (n : ℤ)) hx n).reverse

def verticalExteriorRoute (r : ℕ) (x y z : ℤ)
    (hx : x < -(r : ℤ) ∨ (r : ℤ) < x) :
    (latticeBoxExteriorGraph r).Walk
      (xExteriorVertex r x y hx) (xExteriorVertex r x z hx) := by
  by_cases hy : y ≤ z
  · let n := (z - y).toNat
    have hcast : (n : ℤ) = z - y := Int.toNat_of_nonneg (by omega)
    have hcoord : y + (n : ℤ) = z := by omega
    simpa only [hcoord] using verticalUpExteriorWalk r x y hx n
  · let n := (y - z).toNat
    have hcast : (n : ℤ) = y - z := Int.toNat_of_nonneg (by omega)
    have hcoord : y - (n : ℤ) = z := by omega
    simpa only [hcoord] using verticalDownExteriorWalk r x y hx n

def horizontalExteriorRoute (r : ℕ) (x z y : ℤ)
    (hy : y < -(r : ℤ) ∨ (r : ℤ) < y) :
    (latticeBoxExteriorGraph r).Walk
      (yExteriorVertex r x y hy) (yExteriorVertex r z y hy) := by
  by_cases hx : x ≤ z
  · let n := (z - x).toNat
    have hcast : (n : ℤ) = z - x := Int.toNat_of_nonneg (by omega)
    have hcoord : x + (n : ℤ) = z := by omega
    simpa only [hcoord] using horizontalRightExteriorWalk r x y hy n
  · let n := (x - z).toNat
    have hcast : (n : ℤ) = x - z := Int.toNat_of_nonneg (by omega)
    have hcoord : x - (n : ℤ) = z := by omega
    simpa only [hcoord] using horizontalLeftExteriorWalk r x y hy n

theorem squareLattice_induce_latticeBox_compl_connected (r : ℕ) :
    (squareLattice.induce {v : LatticeVertex | v ∉ latticeBox (0, 0) r}).Connected := by
  classical
  let R : ℤ := (r : ℤ) + 1
  have hR : (r : ℤ) < R := by simp [R]
  let anchor : {v : LatticeVertex // v ∉ latticeBox (0, 0) r} :=
    yExteriorVertex r R R (Or.inr hR)
  rw [connected_iff_exists_forall_reachable]
  refine ⟨anchor, ?_⟩
  intro v
  rcases v with ⟨⟨x,y⟩, hv⟩
  have hout : x < -(r : ℤ) ∨ (r : ℤ) < x ∨
      y < -(r : ℤ) ∨ (r : ℤ) < y := by
    by_contra h
    apply hv
    rw [mem_latticeBox]
    omega
  rcases hout with hx | hx | hy | hy
  · have hyR : R < -(r : ℤ) ∨ (r : ℤ) < R := Or.inr hR
    have hV := verticalExteriorRoute r x y R (Or.inl hx)
    have hH := horizontalExteriorRoute r x R R hyR
    have hbridge : xExteriorVertex r x R (Or.inl hx) =
        yExteriorVertex r x R hyR := by
      apply Subtype.ext
      rfl
    have hroute := hV.append (hbridge ▸ hH)
    have hstart : (⟨(x,y), hv⟩ : {v : LatticeVertex // v ∉ latticeBox (0, 0) r}) =
        xExteriorVertex r x y (Or.inl hx) := by
      apply Subtype.ext
      rfl
    have hend : yExteriorVertex r R R hyR = anchor := by
      apply Subtype.ext
      rfl
    exact (hend ▸ (hstart ▸ hroute.reachable)).symm
  · have hyR : R < -(r : ℤ) ∨ (r : ℤ) < R := Or.inr hR
    have hV := verticalExteriorRoute r x y R (Or.inr hx)
    have hH := horizontalExteriorRoute r x R R hyR
    have hbridge : xExteriorVertex r x R (Or.inr hx) =
        yExteriorVertex r x R hyR := by
      apply Subtype.ext
      rfl
    have hroute := hV.append (hbridge ▸ hH)
    have hstart : (⟨(x,y), hv⟩ : {v : LatticeVertex // v ∉ latticeBox (0, 0) r}) =
        xExteriorVertex r x y (Or.inr hx) := by
      apply Subtype.ext
      rfl
    have hend : yExteriorVertex r R R hyR = anchor := by
      apply Subtype.ext
      rfl
    exact (hend ▸ (hstart ▸ hroute.reachable)).symm
  · have hxR : R < -(r : ℤ) ∨ (r : ℤ) < R := Or.inr hR
    have hH := horizontalExteriorRoute r x R y (Or.inl hy)
    have hV := verticalExteriorRoute r R y R (Or.inr hR)
    have hbridge : yExteriorVertex r R y (Or.inl hy) =
        xExteriorVertex r R y (Or.inr hR) := by
      apply Subtype.ext
      rfl
    have hroute := hH.append (hbridge ▸ hV)
    have hstart : (⟨(x,y), hv⟩ : {v : LatticeVertex // v ∉ latticeBox (0, 0) r}) =
        yExteriorVertex r x y (Or.inl hy) := by
      apply Subtype.ext
      rfl
    have hend : xExteriorVertex r R R (Or.inr hR) = anchor := by
      apply Subtype.ext
      rfl
    exact (hend ▸ (hstart ▸ hroute.reachable)).symm
  · have hxR : R < -(r : ℤ) ∨ (r : ℤ) < R := Or.inr hR
    have hH := horizontalExteriorRoute r x R y (Or.inr hy)
    have hV := verticalExteriorRoute r R y R (Or.inr hR)
    have hbridge : yExteriorVertex r R y (Or.inr hy) =
        xExteriorVertex r R y (Or.inr hR) := by
      apply Subtype.ext
      rfl
    have hroute := hH.append (hbridge ▸ hV)
    have hstart : (⟨(x,y), hv⟩ : {v : LatticeVertex // v ∉ latticeBox (0, 0) r}) =
        yExteriorVertex r x y (Or.inr hy) := by
      apply Subtype.ext
      rfl
    have hend : xExteriorVertex r R R (Or.inr hR) = anchor := by
      apply Subtype.ext
      rfl
    exact (hend ▸ (hstart ▸ hroute.reachable)).symm

end PottsContinuity.FKC.Domains
