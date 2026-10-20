/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarRowConnectivity.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollar
public import Mathlib.Tactic
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK

noncomputable section

local instance rectangleDoubleCollarRowOuterFinite (a : LatticeVertex) (w h : ℕ) :
    Finite (rectangleDoubleCollarOuterVertex a w h) := Finite.of_fintype _

local instance rectangleDoubleCollarRowOuterEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarOuterGraph a w h).edgeSet := Classical.decEq _

def rectangleDoubleCollarRowVertex (a : LatticeVertex) (w h : ℕ)
    (level : ℤ) (hlo : a.2 - 1 ≤ level) (hhi : level ≤ a.2 + (h : ℤ) + 1)
    (i : ℕ) (hi : i ≤ w) : rectangleDoubleCollarOuterVertex a w h :=
  ⟨(a.1 + (i : ℤ), level), by
    rw [mem_latticeRectangle]
    constructor
    · constructor <;> omega
    · exact ⟨hlo, by omega⟩⟩

@[simp] theorem rectangleDoubleCollarRowVertex_val (a : LatticeVertex) (w h : ℕ)
    (level : ℤ) (hlo : a.2 - 1 ≤ level) (hhi : level ≤ a.2 + (h : ℤ) + 1)
    (i : ℕ) (hi : i ≤ w) :
    (rectangleDoubleCollarRowVertex a w h level hlo hhi i hi).val =
      (a.1 + (i : ℤ), level) := rfl

private theorem rectangleDoubleCollar_row_adj (a : LatticeVertex) (w h : ℕ)
    (level : ℤ) (hlo : a.2 - 1 ≤ level) (hhi : level ≤ a.2 + (h : ℤ) + 1)
    (i : ℕ) (hi : i < w) :
    (rectangleDoubleCollarOuterGraph a w h).Adj
      (rectangleDoubleCollarRowVertex a w h level hlo hhi i (by omega))
      (rectangleDoubleCollarRowVertex a w h level hlo hhi (i + 1) (by omega)) := by
  rw [rectangleGraph_adj_iff, squareLattice_adj_iff]
  left
  constructor
  · simp only [rectangleDoubleCollarRowVertex, Subtype.coe_mk, Nat.cast_add,
      Nat.cast_one]
    omega
  · simp [rectangleDoubleCollarRowVertex]

private theorem rectangleDoubleCollar_adj_removed_of_not_image
    (a : LatticeVertex) (w h : ℕ) {u v : rectangleDoubleCollarOuterVertex a w h}
    (hu : u ∉ Set.range (rectangleDoubleCollarEmbedding a w h))
    (hadj : (rectangleDoubleCollarOuterGraph a w h).Adj u v) :
    (⟨s(u,v), (rectangleDoubleCollarOuterGraph a w h).mem_edgeSet.mpr hadj⟩ :
      (rectangleDoubleCollarOuterGraph a w h).edgeSet) ∈ rectangleDoubleCollarRemoved a w h := by
  rw [rectangleDoubleCollarRemoved_mem_iff]
  intro hmap
  have hmapAdj := ((rectangleDoubleCollarInnerGraph a w h).map
    (rectangleDoubleCollarEmbedding a w h)).mem_edgeSet.mp hmap
  obtain ⟨x, y, hxy, hxu, hyv⟩ :=
    (SimpleGraph.map_adj (rectangleDoubleCollarEmbedding a w h)
      (rectangleDoubleCollarInnerGraph a w h) u v).mp hmapAdj
  exact hu ⟨x, hxu⟩

private theorem rectangleDoubleCollar_adj_removed_of_some_not_image
    (a : LatticeVertex) (w h : ℕ) {u v : rectangleDoubleCollarOuterVertex a w h}
    (hout : u ∉ Set.range (rectangleDoubleCollarEmbedding a w h) ∨
      v ∉ Set.range (rectangleDoubleCollarEmbedding a w h))
    (hadj : (rectangleDoubleCollarOuterGraph a w h).Adj u v) :
    (⟨s(u,v), (rectangleDoubleCollarOuterGraph a w h).mem_edgeSet.mpr hadj⟩ :
      (rectangleDoubleCollarOuterGraph a w h).edgeSet) ∈ rectangleDoubleCollarRemoved a w h := by
  rcases hout with hu | hv
  · exact rectangleDoubleCollar_adj_removed_of_not_image a w h hu hadj
  · have hrev := rectangleDoubleCollar_adj_removed_of_not_image a w h hv hadj.symm
    apply (rectangleDoubleCollarRemoved_mem_iff a w h _).2
    intro hmap
    have hmap' : s(v,u) ∈ ((rectangleDoubleCollarInnerGraph a w h).map
        (rectangleDoubleCollarEmbedding a w h)).edgeSet := by
      simpa only [Sym2.eq_swap] using hmap
    exact (rectangleDoubleCollarRemoved_mem_iff a w h _).1 hrev hmap'

private theorem rectangleDoubleCollar_row_step_connected (a : LatticeVertex)
    (w h : ℕ) (level : ℤ) (hlevel : ∀ z : rectangleDoubleCollarInnerVertex a w h,
      z.val.2 ≠ level) (hlo : a.2 - 1 ≤ level)
    (hhi : level ≤ a.2 + (h : ℤ) + 1) (i : ℕ) (hi : i < w) :
    ActualConnected (rectangleDoubleCollarOuterGraph a w h)
      (rectangleDoubleCollarState a w h).val
      (rectangleDoubleCollarRowVertex a w h level hlo hhi i (by omega))
      (rectangleDoubleCollarRowVertex a w h level hlo hhi (i + 1) (by omega)) := by
  have hadj := rectangleDoubleCollar_row_adj a w h level hlo hhi i hi
  apply actualConnected_of_adj
  rw [openGraph_adj]
  refine ⟨⟨s(_, _), (rectangleDoubleCollarOuterGraph a w h).mem_edgeSet.mpr hadj⟩,
    ?_, rfl⟩
  apply rectangleDoubleCollar_adj_removed_of_some_not_image a w h
  · left
    intro hrange
    obtain ⟨z, hz⟩ := hrange
    have hy := congrArg (fun t : rectangleDoubleCollarOuterVertex a w h => t.val.2) hz
    rw [rectangleDoubleCollarEmbedding_val] at hy
    change z.val.2 = level at hy
    exact hlevel z hy
  · exact hadj

private theorem rectangleDoubleCollar_row_reachable_zero (a : LatticeVertex)
    (w h : ℕ) (level : ℤ)
    (hlevel : ∀ z : rectangleDoubleCollarInnerVertex a w h, z.val.2 ≠ level)
    (hlo : a.2 - 1 ≤ level) (hhi : level ≤ a.2 + (h : ℤ) + 1) :
    ∀ i (hi : i ≤ w),
      ActualConnected (rectangleDoubleCollarOuterGraph a w h)
        (rectangleDoubleCollarState a w h).val
        (rectangleDoubleCollarRowVertex a w h level hlo hhi 0 (by omega))
        (rectangleDoubleCollarRowVertex a w h level hlo hhi i hi) := by
  intro i
  induction i with
  | zero => intro hi; exact SimpleGraph.Reachable.refl _
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hstep := rectangleDoubleCollar_row_step_connected a w h level hlevel hlo hhi i (by omega)
      exact hprev.trans hstep

def rectangleDoubleCollarOffset (a : LatticeVertex) (w h : ℕ)
    (v : rectangleDoubleCollarInnerVertex a w h) : ℕ :=
  (v.val.1 - a.1).toNat

lemma rectangleDoubleCollarOffset_le (a : LatticeVertex) (w h : ℕ)
    (v : rectangleDoubleCollarInnerVertex a w h) :
    rectangleDoubleCollarOffset a w h v ≤ w := by
  have hv := (mem_latticeRectangle _ _ _ _).mp v.property
  have hbound : v.val.1 - a.1 ≤ (w : ℤ) := by omega
  exact Int.toNat_le.mpr hbound

lemma rectangleDoubleCollarOffset_cast (a : LatticeVertex) (w h : ℕ)
    (v : rectangleDoubleCollarInnerVertex a w h) :
    ((rectangleDoubleCollarOffset a w h v : ℕ) : ℤ) = v.val.1 - a.1 := by
  exact Int.toNat_of_nonneg (by
    have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    omega)

private theorem rectangleDoubleCollar_inner_to_exterior_row (a : LatticeVertex)
    (w h : ℕ) (level : ℤ)
    (hlevel : ∀ z : rectangleDoubleCollarInnerVertex a w h, z.val.2 ≠ level)
    (hlo : a.2 - 1 ≤ level) (hhi : level ≤ a.2 + (h : ℤ) + 1)
    (v : rectangleDoubleCollarInnerVertex a w h)
    (hv : v.val.2 + 1 = level ∨ level + 1 = v.val.2) :
    ActualConnected (rectangleDoubleCollarOuterGraph a w h)
      (rectangleDoubleCollarState a w h).val
      (rectangleDoubleCollarEmbedding a w h v)
      (rectangleDoubleCollarRowVertex a w h level hlo hhi
        (rectangleDoubleCollarOffset a w h v) (rectangleDoubleCollarOffset_le a w h v)) := by
  have hadj : (rectangleDoubleCollarOuterGraph a w h).Adj
      (rectangleDoubleCollarEmbedding a w h v)
      (rectangleDoubleCollarRowVertex a w h level hlo hhi
        (rectangleDoubleCollarOffset a w h v) (rectangleDoubleCollarOffset_le a w h v)) := by
    rw [rectangleGraph_adj_iff]
    change squareLattice.Adj v.val
      (rectangleDoubleCollarRowVertex a w h level hlo hhi
        (rectangleDoubleCollarOffset a w h v) (rectangleDoubleCollarOffset_le a w h v)).val
    rw [squareLattice_adj_iff]
    right
    constructor
    · have hx : a.1 + (rectangleDoubleCollarOffset a w h v : ℤ) = v.val.1 := by
        rw [rectangleDoubleCollarOffset_cast]
        omega
      simp only [rectangleDoubleCollarRowVertex, Subtype.coe_mk]
      exact hx.symm
    · rcases hv with hv | hv
      · left
        simp only [rectangleDoubleCollarRowVertex, Subtype.coe_mk]
        exact hv
      · right
        simp only [rectangleDoubleCollarRowVertex, Subtype.coe_mk]
        exact hv
  apply actualConnected_of_adj
  rw [openGraph_adj]
  refine ⟨⟨s(_, _), (rectangleDoubleCollarOuterGraph a w h).mem_edgeSet.mpr hadj⟩,
    ?_, rfl⟩
  apply rectangleDoubleCollar_adj_removed_of_some_not_image a w h
  · right
    intro hrange
    obtain ⟨z, hz⟩ := hrange
    have hy := congrArg (fun t : rectangleDoubleCollarOuterVertex a w h => t.val.2) hz
    rw [rectangleDoubleCollarEmbedding_val] at hy
    change z.val.2 = level at hy
    exact hlevel z hy
  · exact hadj

private theorem rectangleDoubleCollar_inner_boundary_connected (a : LatticeVertex)
    (w h : ℕ) (level : ℤ)
    (hlevel : ∀ z : rectangleDoubleCollarInnerVertex a w h, z.val.2 ≠ level)
    (hlo : a.2 - 1 ≤ level) (hhi : level ≤ a.2 + (h : ℤ) + 1)
    (u v : rectangleDoubleCollarInnerVertex a w h)
    (hu : u.val.2 + 1 = level ∨ level + 1 = u.val.2)
    (hv : v.val.2 + 1 = level ∨ level + 1 = v.val.2) :
    ActualConnected (rectangleDoubleCollarOuterGraph a w h)
      (rectangleDoubleCollarState a w h).val
      (rectangleDoubleCollarEmbedding a w h u)
      (rectangleDoubleCollarEmbedding a w h v) := by
  have hurow := rectangleDoubleCollar_inner_to_exterior_row a w h level hlevel hlo hhi u hu
  have hvrow := rectangleDoubleCollar_inner_to_exterior_row a w h level hlevel hlo hhi v hv
  let iu := rectangleDoubleCollarOffset a w h u
  let iv := rectangleDoubleCollarOffset a w h v
  have hrootu := rectangleDoubleCollar_row_reachable_zero a w h level hlevel hlo hhi iu
    (rectangleDoubleCollarOffset_le a w h u)
  have hrootv := rectangleDoubleCollar_row_reachable_zero a w h level hlevel hlo hhi iv
    (rectangleDoubleCollarOffset_le a w h v)
  have hrows : ActualConnected (rectangleDoubleCollarOuterGraph a w h)
      (rectangleDoubleCollarState a w h).val
      (rectangleDoubleCollarRowVertex a w h level hlo hhi iu (rectangleDoubleCollarOffset_le a w h u))
      (rectangleDoubleCollarRowVertex a w h level hlo hhi iv (rectangleDoubleCollarOffset_le a w h v)) :=
    hrootu.symm.trans hrootv
  exact hurow.trans (hrows.trans hvrow.symm)

/-- Any two embedded inner bottom-row vertices connect through the open removed
bottom collar, using actual open edges only. -/
theorem rectangleDoubleCollar_bottom_row_connected (a : LatticeVertex)
    (w h : ℕ) (u v : rectangleDoubleCollarInnerVertex a w h)
    (hu : u.val.2 = a.2) (hv : v.val.2 = a.2) :
    ActualConnected (rectangleDoubleCollarOuterGraph a w h)
      (rectangleDoubleCollarState a w h).val
      (rectangleDoubleCollarEmbedding a w h u)
      (rectangleDoubleCollarEmbedding a w h v) := by
  apply rectangleDoubleCollar_inner_boundary_connected a w h (a.2 - 1)
    (fun z => by
      have hz := (mem_latticeRectangle _ _ _ _).mp z.property
      omega) (by omega) (by omega)
  · right
    rw [hu]
    omega
  · right
    rw [hv]
    omega

/-- Any two embedded inner top-row vertices connect through the open removed
top collar, using actual open edges only. -/
theorem rectangleDoubleCollar_top_row_connected (a : LatticeVertex)
    (w h : ℕ) (u v : rectangleDoubleCollarInnerVertex a w h)
    (hu : u.val.2 = a.2 + (h : ℤ)) (hv : v.val.2 = a.2 + (h : ℤ)) :
    ActualConnected (rectangleDoubleCollarOuterGraph a w h)
      (rectangleDoubleCollarState a w h).val
      (rectangleDoubleCollarEmbedding a w h u)
      (rectangleDoubleCollarEmbedding a w h v) := by
  apply rectangleDoubleCollar_inner_boundary_connected a w h
    (a.2 + (h : ℤ) + 1)
    (fun z => by
      have hz := (mem_latticeRectangle _ _ _ _).mp z.property
      omega) (by omega) (by omega)
  · left
    rw [hu]
  · left
    rw [hv]

end
end PottsContinuity.PlanarMixed.Square
