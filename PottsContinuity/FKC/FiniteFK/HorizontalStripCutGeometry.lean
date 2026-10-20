-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripCutGeometry.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeight
public import PottsContinuity.FKC.Medial.WholePlaneClusterContainment

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open Finset

/-- The normalized horizontal primal bond crossing column `k` at height `y`. -/
def horizontalStripCutBond (k : ℤ) (y : ℕ) : LatticeBond :=
  ⟨(k, (y : ℤ)), LatticeAxis.horizontal⟩

/-- Original unoriented square-lattice edges crossing the vertical cut after
column `k`, restricted to the strip rows `0,...,2*n`. -/
def horizontalStripCutEdges (n : ℕ) (k : ℤ) : Finset squareLattice.edgeSet :=
  (Finset.range (2 * n + 1)).image (fun y => latticeBondEdge (horizontalStripCutBond k y))

theorem horizontalStripCutEdges_disjoint_of_ne (n : ℕ) {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (horizontalStripCutEdges n k) (horizontalStripCutEdges n l) := by
  rw [Finset.disjoint_left]
  intro e heK heL
  rcases Finset.mem_image.mp heK with ⟨y, hy, rfl⟩
  rcases Finset.mem_image.mp heL with ⟨z, hz, heq⟩
  have hb : horizontalStripCutBond k y = horizontalStripCutBond l z :=
    LatticeBond.toSym2_injective (congrArg Subtype.val heq).symm
  have hbase := congrArg LatticeBond.base hb
  exact hkl (congrArg Prod.fst hbase)

private theorem horizontalStripCutEdges_mem (n : ℕ) (k : ℤ) (y : ℕ)
    (hy : y ≤ 2 * n) :
    latticeBondEdge (horizontalStripCutBond k y) ∈ horizontalStripCutEdges n k := by
  apply Finset.mem_image.mpr
  exact ⟨y, Finset.mem_range.mpr (by omega), rfl⟩

private theorem horizontalStripAdjacent_crosses_cut
    (n : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    (u v : horizontalStripVertex n)
    (hadj : (horizontalStripOpenGraph n ω).Adj u v)
    (hu : u.1.1 ≤ k) (hv : k < v.1.1) :
    ∃ y : ℕ, y ≤ 2 * n ∧
      latticeBondEdge (horizontalStripCutBond k y) ∈ horizontalStripCutEdges n k ∧
      Sym2.map Subtype.val s(u, v) =
        (latticeBondEdge (horizontalStripCutBond k y)).val ∧
      latticeConfigurationBondState ω (horizontalStripCutBond k y) = true := by
  have hwhole : (wholePlaneOpenPrimalGraph ω).Adj u.1 v.1 := hadj
  rcases hwhole with ⟨hadj', hopen⟩
  have hcoords := hadj'
  change ((u.1.1 + 1 = v.1.1 ∨ v.1.1 + 1 = u.1.1) ∧ u.1.2 = v.1.2) ∨
    (u.1.1 = v.1.1 ∧ (u.1.2 + 1 = v.1.2 ∨ v.1.2 + 1 = u.1.2)) at hcoords
  have hx : v.1.1 = u.1.1 + 1 := by
    rcases hcoords with ⟨hxy, _⟩ | ⟨hxx, _⟩
    · rcases hxy with h | h
      · omega
      · omega
    · omega
  have hyInt : u.1.2 = v.1.2 := by
    rcases hcoords with ⟨_, h⟩ | ⟨hxx, h⟩
    · exact h
    · omega
  have huk : u.1.1 = k := by omega
  have hvk : v.1.1 = k + 1 := by omega
  have hyNonneg : 0 ≤ u.1.2 := u.2.1
  let y : ℕ := Int.toNat u.1.2
  have hyCast : (y : ℤ) = u.1.2 := by
    dsimp [y]
    exact Int.toNat_of_nonneg hyNonneg
  have hyBoundInt : u.1.2 ≤ 2 * (n : ℤ) := u.2.2
  have hyBound : y ≤ 2 * n := by
    have hcast : (y : ℤ) ≤ 2 * (n : ℤ) := by simpa [hyCast] using hyBoundInt
    exact_mod_cast hcast
  have hsource : (horizontalStripCutBond k y).source = u.1 := by
    ext <;> simp [horizontalStripCutBond, LatticeBond.source, huk, hyCast]
  have htarget : (horizontalStripCutBond k y).target = v.1 := by
    ext <;> simp [horizontalStripCutBond, LatticeBond.target, hvk, hyInt, hyCast]
  have hbondAdj : (wholePlaneOpenPrimalGraph ω).Adj
      (horizontalStripCutBond k y).source (horizontalStripCutBond k y).target := by
    rw [hsource, htarget]
    exact ⟨hadj', hopen⟩
  have hstate := (wholePlaneOpenPrimalGraph_adj_bond ω (horizontalStripCutBond k y)).mp hbondAdj
  refine ⟨y, hyBound, horizontalStripCutEdges_mem n k y hyBound, ?_, hstate⟩
  apply Sym2.eq_iff.mpr
  exact Or.inl ⟨by simp [hsource], by simp [htarget]⟩

theorem horizontalStripWalk_usesCutEdge
    (n : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk u v)
    (hu : u.1.1 ≤ k) (hv : k < v.1.1) :
    ∃ e ∈ p.edges, ∃ y : ℕ, y ≤ 2 * n ∧
      latticeBondEdge (horizontalStripCutBond k y) ∈ horizontalStripCutEdges n k ∧
      Sym2.map Subtype.val e = (latticeBondEdge (horizontalStripCutBond k y)).val ∧
      latticeConfigurationBondState ω (horizontalStripCutBond k y) = true := by
  induction p with
  | nil => omega
  | @cons a b c hadj tail ih =>
      by_cases hcross : k < b.1.1
      · obtain ⟨y, hy, hemem, heq, hopen⟩ :=
          horizontalStripAdjacent_crosses_cut n ω k a b hadj hu hcross
        refine ⟨s(a, b), ?_, y, hy, hemem, ?_, hopen⟩
        · simp [SimpleGraph.Walk.edges_cons]
        · simpa using heq
      · have hb : b.1.1 ≤ k := le_of_not_gt hcross
        obtain ⟨e, he, y, hy, hemem, heq, hopen⟩ := ih hb hv
        exact ⟨e, by simpa [SimpleGraph.Walk.edges_cons] using List.mem_cons_of_mem _ he,
          y, hy, hemem, heq, hopen⟩

theorem horizontalStripClosedCut_not_reachable
    (n : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    (u v : horizontalStripVertex n)
    (hu : u.1.1 ≤ k) (hv : k < v.1.1)
    (hclosed : ∀ e ∈ horizontalStripCutEdges n k, ω e = false) :
    ¬ (horizontalStripOpenGraph n ω).Reachable u v := by
  intro hreach
  rcases hreach with ⟨p⟩
  obtain ⟨e, he, y, hy, hemem, heq, hopen⟩ :=
    horizontalStripWalk_usesCutEdge n ω k p hu hv
  have hfalse := hclosed (latticeBondEdge (horizontalStripCutBond k y)) hemem
  change ω (latticeBondEdge (horizontalStripCutBond k y)) = true at hopen
  rw [hfalse] at hopen
  cases hopen

