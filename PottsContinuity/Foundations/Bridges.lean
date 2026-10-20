module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.PD.Defs.Box
public import PottsContinuity.PD.Defs.RCFreeClusterCount
public import PottsContinuity.PD.Defs.RCInfiniteOpenGraph
public import PottsContinuity.PD.Defs.RCProb
public import PottsContinuity.PD.Defs.RCWeight
public import PottsContinuity.PD.Defs.VertexBoundary

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Foundations

open Classical

theorem squareLattice_eq_PD :
    PottsContinuity.squareLattice = PottsContinuity.PD.squareLattice := rfl

theorem box_eq_PD (n : ℕ) :
    PottsContinuity.box n = PottsContinuity.PD.box n := rfl

theorem rcOpenGraph_eq_PD (V : Finset (ℤ × ℤ))
    (ω : (PottsContinuity.squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    PottsContinuity.rcOpenGraph V ω = PottsContinuity.PD.rcOpenGraph V ω := rfl

theorem rcInfiniteOpenGraph_eq_PD (ω : PottsContinuity.squareLattice.edgeSet → Bool) :
    PottsContinuity.rcInfiniteOpenGraph ω =
      PottsContinuity.PD.rcInfiniteOpenGraph ω := rfl

theorem rcFreeClusterCount_eq_PD (V : Finset (ℤ × ℤ))
    (ω : (PottsContinuity.squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    PottsContinuity.rcFreeClusterCount V ω =
      PottsContinuity.PD.rcFreeClusterCount V ω := rfl

private theorem adj_iff (x y : ℤ × ℤ) :
    PottsContinuity.squareLattice.Adj x y ↔
      y = (x.1 + 1, x.2) ∨ y = (x.1 - 1, x.2) ∨
        y = (x.1, x.2 + 1) ∨ y = (x.1, x.2 - 1) := by
  change |x.1 - y.1| + |x.2 - y.2| = 1 ↔ _
  simp only [abs_eq_max_neg, Prod.ext_iff]
  omega

private theorem nbr_eq (x : ℤ × ℤ) :
    {y | PottsContinuity.squareLattice.Adj x y} =
      ({(x.1 + 1, x.2), (x.1 - 1, x.2),
        (x.1, x.2 + 1), (x.1, x.2 - 1)} : Finset (ℤ × ℤ)) := by
  ext y
  simp only [Set.mem_ofPred_eq, adj_iff, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]

private theorem card_nbr (x : ℤ × ℤ) :
    ({(x.1 + 1, x.2), (x.1 - 1, x.2),
      (x.1, x.2 + 1), (x.1, x.2 - 1)} : Finset (ℤ × ℤ)).card = 4 := by
  classical
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [Prod.ext_iff]
    omega
  · simp [Prod.ext_iff]
  · simp [Prod.ext_iff]
    omega

theorem vertexBoundary_eq_PD (V : Finset (ℤ × ℤ)) :
    PottsContinuity.vertexBoundary V = PottsContinuity.PD.vertexBoundary V := by
  classical
  ext x
  simp only [PottsContinuity.vertexBoundary,
    PottsContinuity.PD.vertexBoundary, Set.mem_ofPred_eq,
    and_congr_right_iff]
  intro hx
  have hsub : {y | y ∈ V ∧ PottsContinuity.squareLattice.Adj x y} ⊆
      {y | PottsContinuity.squareLattice.Adj x y} := fun _ hy => hy.2
  have hfinN : ({y | PottsContinuity.squareLattice.Adj x y} : Set (ℤ × ℤ)).Finite := by
    rw [nbr_eq]
    exact Finset.finite_toSet _
  have hcardN : ({y | PottsContinuity.squareLattice.Adj x y} : Set (ℤ × ℤ)).ncard = 4 := by
    rw [nbr_eq, Set.ncard_coe_finset, card_nbr]
  constructor
  · intro h
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    have heq : {y | y ∈ V ∧ PottsContinuity.squareLattice.Adj x y} =
        {y | PottsContinuity.squareLattice.Adj x y} := by
      ext y
      constructor
      · exact And.right
      · intro hy
        exact ⟨hno y hy, hy⟩
    rw [heq, hcardN] at h
    omega
  · rintro ⟨y, hy, hyV⟩
    have hss : {y | y ∈ V ∧ PottsContinuity.squareLattice.Adj x y} ⊂
        {y | PottsContinuity.squareLattice.Adj x y} :=
      ⟨hsub, fun h2 => hyV (h2 hy).1⟩
    have hlt := Set.ncard_lt_ncard hss hfinN
    omega

theorem rcWiredClusterCount_eq_PD (V : Finset (ℤ × ℤ))
    (ω : (PottsContinuity.squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    PottsContinuity.rcWiredClusterCount V ω =
      PottsContinuity.PD.rcWiredClusterCount V ω := by
  unfold PottsContinuity.rcWiredClusterCount
    PottsContinuity.PD.rcWiredClusterCount
  rw [rcOpenGraph_eq_PD, vertexBoundary_eq_PD]

theorem rcWeight_eq_PD (V : Finset (ℤ × ℤ)) (p q : ℝ) (i : Fin 2)
    (ω : (PottsContinuity.squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    PottsContinuity.rcWeight V p q i ω =
      PottsContinuity.PD.rcWeight V p q i ω := by
  unfold PottsContinuity.rcWeight PottsContinuity.PD.rcWeight
  rw [rcFreeClusterCount_eq_PD, rcWiredClusterCount_eq_PD]
  rfl

theorem rcProb_eq_PD (V : Finset (ℤ × ℤ)) (p : Set.Icc (0 : ℝ) 1)
    (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (ω : (PottsContinuity.squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    PottsContinuity.rcProb V p q i ω =
      PottsContinuity.PD.rcProb V p q i ω := by
  unfold PottsContinuity.rcProb PottsContinuity.PD.rcProb
  simp_rw [rcWeight_eq_PD]
  rfl

end PottsContinuity.Foundations
