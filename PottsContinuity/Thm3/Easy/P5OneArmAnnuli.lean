module

public import Mathlib
public import PottsContinuity.PD.Duality.BondStates
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting
public import PottsContinuity.PD.RCInfinite.ExteriorClusters
public import PottsContinuity.DualityExt.AnnulusCounterexample
public import PottsContinuity.FKC.FiniteFK.OutsidePathLocalization
public import PottsContinuity.Thm3.Easy.P5AnnuliProduct

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.RCInfinite
open PottsContinuity.PD.Duality
open PottsContinuity.DualityExt

private theorem walk_first_entry_with_support_subset
    {V : Type*} (G : SimpleGraph V) (B : Set V) {u v : V}
    (p : G.Walk u v) (hu : u ∉ B) (hv : v ∈ B) :
    ∃ x, x ∈ B ∧ ∃ w, G.Adj w x ∧ w ∉ B ∧
      ∃ q : G.Walk u w,
        (∀ y ∈ q.support, y ∉ B) ∧
        (∀ y ∈ q.support, y ∈ p.support) := by
  induction p with
  | nil => exact False.elim (hu hv)
  | @cons u z v h p ih =>
      by_cases hz : z ∈ B
      · refine ⟨z, hz, u, h, hu, .nil, ?_, ?_⟩
        · intro y hy
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
          subst y
          exact hu
        · intro y hy
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
          subst y
          exact SimpleGraph.Walk.start_mem_support _
      · obtain ⟨x, hx, w, hw, hwo, q, hqout, hqsub⟩ := ih hz hv
        refine ⟨x, hx, w, hw, hwo, .cons h q, ?_, ?_⟩
        · intro y hy
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hu
          · exact hqout y hy
        · intro y hy
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact SimpleGraph.Walk.start_mem_support _
          · exact (SimpleGraph.Walk.support_subset_support_cons p h) (hqsub y hy)

private theorem walk_map_of_support
    {V : Type*} {G H : SimpleGraph V} {u v : V}
    (P : V → Prop) (p : G.Walk u v)
    (hP : ∀ x ∈ p.support, P x)
    (hAdj : ∀ a b, G.Adj a b → P a → P b → H.Adj a b) : H.Reachable u v := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u z v h p ih =>
      have hu : P u := hP u (by simp)
      have hz : P z := hP z (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have htail : ∀ x ∈ p.support, P x := fun x hx => hP x (by
        simp [SimpleGraph.Walk.support_cons, hx])
      exact (hAdj u z h hu hz).reachable.trans (ih htail)

private theorem box_boundary_vertex_not_smaller_box
    (N R : ℕ) (hRN : R < N) {y : LatticeVertex}
    (hy : y ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) N)) :
    y ∉ latticeBox (0, 0) R := by
  intro hyR
  have hside := PottsContinuity.PD.RCInfinite.box_boundary_coordinate_edge N hy
  have hcoords := (mem_latticeBox (0, 0) y R).1 hyR
  have hRNz : (R : ℤ) < (N : ℤ) := by exact_mod_cast hRN
  rcases hside with h | h | h | h <;>
    rw [h] at hcoords <;> omega

/-- An annulus path whose inner endpoint is adjacent to the removed inner box.
This excludes the corner-start paths that do not meet the inner boundary
class of the annulus. -/
def annulusInnerSideOpenCrossing (r : ℕ) (ω : LatticeConfiguration) : Prop :=
  ∃ x y : LatticeVertex,
    x ∈ annulusVertexSet r ∧
    (∃ u, u ∈ latticeBox (0, 0) (r - 1) ∧ squareLattice.Adj u x) ∧
    y ∈ annulusOuterBoundary (2 * r) ∧
    (annulusOpenGraph r ω).Reachable x y

/-- Every one-arm path to a larger square boundary crosses each intervening
full-inner-box annulus. The path is cut after its last visit to the smaller
box, so all retained vertices lie in the induced annulus graph. -/
theorem oneArmBoundary_forces_dyadicAnnulusInnerSideOpenCrossing
    (n j : ℕ) (hj : 3 ≤ j) (hscale : 2 ^ j < n)
    (ω : LatticeConfiguration)
    (hOneArm : ∃ y ∈ PottsContinuity.PD.vertexBoundary
        (latticeBox (0, 0) n),
      (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y) :
    annulusInnerSideOpenCrossing (2 ^ (j - 1)) ω := by
  rcases hOneArm with ⟨y, hy, hreach⟩
  let r := 2 ^ (j - 1)
  let R := 2 ^ j
  have hrpos : 1 ≤ r := by
    dsimp [r]
    have hpow : 0 < 2 ^ (j - 1) := Nat.pow_pos (by omega)
    omega
  have hrad : 2 * r = R := by
    dsimp [r, R]
    calc
      2 * 2 ^ (j - 1) = 2 ^ (j - 1) * 2 := by omega
      _ = 2 ^ ((j - 1) + 1) := by rw [Nat.pow_succ]
      _ = 2 ^ j := by congr 1; omega
  have hyOutside : y ∉ latticeBox (0, 0) R :=
    box_boundary_vertex_not_smaller_box n R hscale hy
  have hreachWhole : (wholePlaneOpenPrimalGraph ω).Reachable (0, 0) y := by
    simpa only [wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph] using hreach
  rcases hreachWhole with ⟨w⟩
  obtain ⟨z, hzBox, wPrefix, hprefixBox, y', hzy', hy'⟩ :=
    PottsContinuity.PD.RCInfinite.walk_prefix_to_boundary w
      (center_mem_latticeBox (0, 0) R) hyOutside
  have hzAdj : squareLattice.Adj z y' := hzy'.choose
  have hzBoundary :
      z ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) R) :=
    ⟨hzBox, y', hzAdj, hy'⟩
  have hzSide := PottsContinuity.PD.RCInfinite.box_boundary_coordinate_edge R hzBoundary
  have hzOuter : z ∈ annulusOuterBoundary R := by
    have hzSide' : z.1 = (R : ℤ) ∨ z.1 = -(R : ℤ) ∨
        z.2 = (R : ℤ) ∨ z.2 = -(R : ℤ) := by
      rcases hzSide with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    exact Finset.mem_filter.mpr ⟨hzBox, hzSide'⟩
  have hzNotInner : z ∉ latticeBox (0, 0) (r - 1) := by
    intro h
    have hzNotR := annulusOuterBoundary_not_innerBox r hrpos
      (by simpa [hrad] using hzOuter)
    exact hzNotR (latticeBox_mono (0, 0) (Nat.sub_le r 1) h)
  let B : Set LatticeVertex := latticeBox (0, 0) (r - 1)
  have hOriginB : (0, 0) ∈ B := by
    exact center_mem_latticeBox (0, 0) (r - 1)
  have hzNotB : z ∉ B := by simpa [B] using hzNotInner
  obtain ⟨x, hxB, x', hxx', hx'NotB, q, hqNotB, hqSub⟩ :=
    walk_first_entry_with_support_subset (wholePlaneOpenPrimalGraph ω) B
      wPrefix.reverse hzNotB hOriginB
  have hxx'Sq : squareLattice.Adj x' x := hxx'.choose
  have hx'Box : x' ∈ latticeBox (0, 0) r := by
    have hxs : x ∈ latticeBox (0, 0) (r - 1) := by simpa [B] using hxB
    have h := lattice_adj_box_succ hxx'Sq.symm hxs
    simpa [Nat.sub_add_cancel hrpos] using h
  have htailBox : ∀ a ∈ q.reverse.support, a ∈ latticeBox (0, 0) R := by
    intro a ha
    have hasub : a ∈ wPrefix.reverse.support := hqSub a (by
      simpa [SimpleGraph.Walk.support_reverse] using ha)
    have habox := hprefixBox a (by
      simpa [SimpleGraph.Walk.support_reverse] using hasub)
    exact habox
  have htailOutside : ∀ a ∈ q.reverse.support, a ∉ B := by
    intro a ha
    exact hqNotB a (by simpa [SimpleGraph.Walk.support_reverse] using ha)
  have hP : ∀ a ∈ q.reverse.support,
      a ∈ latticeBox (0, 0) R ∧ a ∉ latticeBox (0, 0) (r - 1) := by
    intro a ha
    exact ⟨htailBox a ha, by simpa [B] using htailOutside a ha⟩
  have hAnnReach : (annulusOpenGraph r ω).Reachable x' z := by
    apply walk_map_of_support
      (fun a => a ∈ latticeBox (0, 0) R ∧
        a ∉ latticeBox (0, 0) (r - 1)) q.reverse hP
    intro a b hab ha hb
    rcases hab with ⟨habSq, hopen⟩
    change a ∈ annulusVertexSet r ∧ b ∈ annulusVertexSet r ∧
      (wholePlaneOpenPrimalGraph ω).Adj a b
    have haOuter : a ∈ latticeBox (0, 0) (2 * r) := by simpa [hrad] using ha.1
    have hbOuter : b ∈ latticeBox (0, 0) (2 * r) := by simpa [hrad] using hb.1
    exact ⟨Finset.mem_sdiff.mpr ⟨haOuter, ha.2⟩,
      Finset.mem_sdiff.mpr ⟨hbOuter, hb.2⟩, ⟨habSq, hopen⟩⟩
  have hx'Outer : x' ∈ latticeBox (0, 0) (2 * r) :=
    latticeBox_mono (0, 0) (by omega) hx'Box
  have hx'Vertex : x' ∈ annulusVertexSet r :=
    Finset.mem_sdiff.mpr ⟨hx'Outer, hx'NotB⟩
  have hfinal : annulusInnerSideOpenCrossing r ω := by
    exact ⟨x', z, hx'Vertex, ⟨x, hxB, hxx'Sq.symm⟩,
      by simpa [R, hrad] using hzOuter, hAnnReach⟩
  simpa [r] using hfinal

/-- The boundary-adjacent form immediately gives the broader annulus
crossing used by the existing dyadic product. -/
theorem oneArmBoundary_forces_dyadicAnnulusOpenCrossing
    (n j : ℕ) (hj : 3 ≤ j) (hscale : 2 ^ j < n)
    (ω : LatticeConfiguration)
    (hOneArm : ∃ y ∈ PottsContinuity.PD.vertexBoundary
        (latticeBox (0, 0) n),
      (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y) :
    ω ∈ dyadicAnnulusOpenCrossingEvent j := by
  obtain ⟨x, y, hx, _, hy, hreach⟩ :=
    oneArmBoundary_forces_dyadicAnnulusInnerSideOpenCrossing
      n j hj hscale ω hOneArm
  have hxbox : x ∈ latticeBox (0, 0) (2 ^ (j - 1)) := by
    obtain ⟨u, hu, hux⟩ := ‹∃ u, u ∈ latticeBox (0, 0)
        (2 ^ (j - 1) - 1) ∧ squareLattice.Adj u x›
    have hrpos : 1 ≤ 2 ^ (j - 1) := by
      have hpow : 0 < 2 ^ (j - 1) := Nat.pow_pos (by omega)
      omega
    have h := lattice_adj_box_succ hux hu
    simpa [Nat.sub_add_cancel hrpos] using h
  exact ⟨x, y, hxbox, hy, hreach⟩

end PottsContinuity.Thm3.Easy
