-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/BoxConnector.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.FK.Lattice
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

private theorem boxVertex_bounds {n : ℕ} (x : BoxVertex (0, 0) n) :
    (-(n : ℤ) ≤ x.val.1 ∧ x.val.1 ≤ n) ∧
      (-(n : ℤ) ≤ x.val.2 ∧ x.val.2 ≤ n) := by
  have hx := x.property
  rw [mem_latticeBox] at hx
  simpa only [Prod.fst_zero, Prod.snd_zero, zero_sub, zero_add] using hx

private theorem box_mem_of_bounds {n : ℕ} {x : LatticeVertex}
    (hx1 : -(n : ℤ) ≤ x.1) (hx2 : x.1 ≤ n)
    (hy1 : -(n : ℤ) ≤ x.2) (hy2 : x.2 ≤ n) :
    x ∈ latticeBox (0, 0) n := by
  rw [mem_latticeBox]
  simpa only [Prod.fst_zero, Prod.snd_zero, zero_sub, zero_add] using
    (show (-(n : ℤ) ≤ x.1 ∧ x.1 ≤ n) ∧
      (-(n : ℤ) ≤ x.2 ∧ x.2 ≤ n) from ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩)

private theorem box_horizontal_up {n : ℕ} {a b y : ℤ}
    (ha : -(n : ℤ) ≤ a) (hb : b ≤ n) (hy₁ : -(n : ℤ) ≤ y) (hy₂ : y ≤ n)
    (hab : a ≤ b) :
    (boxGraph (0, 0) n).Reachable
      ⟨(a, y), box_mem_of_bounds ha (by omega) hy₁ hy₂⟩
      ⟨(b, y), box_mem_of_bounds (by omega) hb hy₁ hy₂⟩ := by
  let d : ℕ := (b - a).toNat
  have hd : (d : ℤ) = b - a := by
    dsimp [d]
    exact Int.toNat_of_nonneg (by omega)
  have hcoord (k : ℕ) (hk : k ≤ d) :
      -(n : ℤ) ≤ a + (k : ℤ) ∧ a + (k : ℤ) ≤ n := by
    have hkz : (k : ℤ) ≤ (d : ℤ) := by exact_mod_cast hk
    refine ⟨by omega, ?_⟩
    calc
      a + (k : ℤ) ≤ a + (d : ℤ) := add_le_add_right hkz a
      _ = b := by rw [hd]; ring
      _ ≤ n := hb
  have hwalk : ∀ (k : ℕ) (hk : k ≤ d),
      (boxGraph (0, 0) n).Reachable
        ⟨(a, y), box_mem_of_bounds ha (by omega) hy₁ hy₂⟩
        ⟨(a + (k : ℤ), y), box_mem_of_bounds (hcoord k hk).1
          (hcoord k hk).2 hy₁ hy₂⟩ := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [Nat.cast_zero, add_zero] using
          (SimpleGraph.Reachable.refl
            (⟨(a, y), box_mem_of_bounds ha (by omega) hy₁ hy₂⟩ : BoxVertex (0, 0) n))
    | succ k ih =>
        intro hk
        have hk' : k ≤ d := Nat.le_of_succ_le hk
        let xk : BoxVertex (0, 0) n :=
          ⟨(a + (k : ℤ), y), box_mem_of_bounds (hcoord k hk').1
            (hcoord k hk').2 hy₁ hy₂⟩
        let xnext : BoxVertex (0, 0) n :=
          ⟨(a + ((k + 1 : ℕ) : ℤ), y),
            box_mem_of_bounds (hcoord (k + 1) hk).1
              (hcoord (k + 1) hk).2 hy₁ hy₂⟩
        have hadj : (boxGraph (0, 0) n).Adj xk xnext := by
          apply (boxGraph_adj_iff (0, 0) n xk xnext).2
          rw [squareLattice_adj_iff]
          left
          constructor
          · simp [xk, xnext, Nat.cast_succ, add_assoc]
          · rfl
        have hr := (ih hk').trans hadj.reachable
        simpa only [xk, xnext, Nat.cast_succ, add_assoc] using hr
  have hbound : d ≤ d := le_rfl
  have hr := hwalk d hbound
  have hend : a + (d : ℤ) = b := by rw [hd]; ring
  simpa only [hend] using hr

private theorem box_vertical_up {n : ℕ} {x a b : ℤ}
    (hx₁ : -(n : ℤ) ≤ x) (hx₂ : x ≤ n) (ha : -(n : ℤ) ≤ a) (hb : b ≤ n)
    (hab : a ≤ b) :
    (boxGraph (0, 0) n).Reachable
      ⟨(x, a), box_mem_of_bounds hx₁ hx₂ ha (by omega)⟩
      ⟨(x, b), box_mem_of_bounds hx₁ hx₂ (by omega) hb⟩ := by
  let d : ℕ := (b - a).toNat
  have hd : (d : ℤ) = b - a := by
    dsimp [d]
    exact Int.toNat_of_nonneg (by omega)
  have hcoord (k : ℕ) (hk : k ≤ d) :
      -(n : ℤ) ≤ a + (k : ℤ) ∧ a + (k : ℤ) ≤ n := by
    have hkz : (k : ℤ) ≤ (d : ℤ) := by exact_mod_cast hk
    refine ⟨by omega, ?_⟩
    calc
      a + (k : ℤ) ≤ a + (d : ℤ) := add_le_add_right hkz a
      _ = b := by rw [hd]; ring
      _ ≤ n := hb
  have hwalk : ∀ (k : ℕ) (hk : k ≤ d),
      (boxGraph (0, 0) n).Reachable
        ⟨(x, a), box_mem_of_bounds hx₁ hx₂ ha (by omega)⟩
        ⟨(x, a + (k : ℤ)), box_mem_of_bounds hx₁ hx₂ (hcoord k hk).1
          (hcoord k hk).2⟩ := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [Nat.cast_zero, add_zero] using
          (SimpleGraph.Reachable.refl
            (⟨(x, a), box_mem_of_bounds hx₁ hx₂ ha (by omega)⟩ : BoxVertex (0, 0) n))
    | succ k ih =>
        intro hk
        have hk' : k ≤ d := Nat.le_of_succ_le hk
        let xk : BoxVertex (0, 0) n :=
          ⟨(x, a + (k : ℤ)), box_mem_of_bounds hx₁ hx₂ (hcoord k hk').1
            (hcoord k hk').2⟩
        let xnext : BoxVertex (0, 0) n :=
          ⟨(x, a + ((k + 1 : ℕ) : ℤ)), box_mem_of_bounds hx₁ hx₂
            (hcoord (k + 1) hk).1 (hcoord (k + 1) hk).2⟩
        have hadj : (boxGraph (0, 0) n).Adj xk xnext := by
          apply (boxGraph_adj_iff (0, 0) n xk xnext).2
          rw [squareLattice_adj_iff]
          right
          constructor
          · rfl
          · simp [xk, xnext, Nat.cast_succ, add_assoc]
        have hr := (ih hk').trans hadj.reachable
        simpa only [xk, xnext, Nat.cast_succ, add_assoc] using hr
  have hr := hwalk d le_rfl
  have hend : a + (d : ℤ) = b := by rw [hd]; ring
  simpa only [hend] using hr

/-- The graph induced on a centered finite square box is connected. -/
theorem boxGraph_connected (n : ℕ) : (boxGraph (0, 0) n).Connected := by
  let : Nonempty (BoxVertex (0, 0) n) :=
    ⟨⟨(0, 0), center_mem_latticeBox (0, 0) n⟩⟩
  refine ⟨?_⟩
  intro u v
  have hu := boxVertex_bounds u
  have hv := boxVertex_bounds v
  have hhor : (boxGraph (0, 0) n).Reachable u
      ⟨(v.val.1, u.val.2), box_mem_of_bounds (by omega) (by omega) hu.2.1 hu.2.2⟩ := by
    by_cases hxy : u.val.1 ≤ v.val.1
    · exact box_horizontal_up hu.1.1 hv.1.2 hu.2.1 hu.2.2 hxy
    · have hr := box_horizontal_up hv.1.1 hu.1.2 hu.2.1 hu.2.2 (by omega)
      simpa only [Subtype.mk.injEq] using hr.symm
  have hver : (boxGraph (0, 0) n).Reachable
      ⟨(v.val.1, u.val.2), box_mem_of_bounds (by omega) (by omega) hu.2.1 hu.2.2⟩ v := by
    by_cases hxy : u.val.2 ≤ v.val.2
    · exact box_vertical_up (by omega) (by omega) hu.2.1 hv.2.2 hxy
    · have hr := box_vertical_up hv.1.1 hv.1.2 hv.2.1 hu.2.2 (by omega)
      simpa only [Subtype.mk.injEq] using hr.symm
  exact hhor.trans hver

end
end PottsContinuity.PD.RCInfinite
