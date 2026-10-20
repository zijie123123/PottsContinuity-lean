module

public import PottsContinuity.PlanarTopology.HorizontalWalks
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- A simple cap between two distinct top vertices, entirely at height N+1
apart from its endpoints. It uses no bond with both endpoints at height at
most N. Its horizontal range is exactly bounded by the two endpoint columns. -/
theorem exists_top_cap_path (N : ℕ) (x y : ℤ) (hxy : x ≠ y) :
    ∃ p : PD.FK.squareLattice.Walk (x,(N : ℤ)) (y,(N : ℤ)),
      p.IsPath ∧ 1 < p.length ∧
      (∀ z ∈ p.support, min x y ≤ z.1 ∧ z.1 ≤ max x y ∧
        (N : ℤ) ≤ z.2 ∧ z.2 ≤ (N : ℤ)+1) ∧
      (∀ z ∈ p.support, z.2 ≤ (N : ℤ) → z=(x,(N : ℤ)) ∨ z=(y,(N : ℤ))) ∧
      ∀ a b : LatticeVertex, a.2 ≤ (N : ℤ) → b.2 ≤ (N : ℤ) → s(a,b) ∉ p.edges := by
  classical
  obtain ⟨w,hw⟩ := PlanarTopology.horizontal_walk_between x y ((N : ℤ)+1)
  let q := w.toPath.val
  have hq : q.IsPath := w.toPath.property
  have hqs : ∀ z ∈ q.support, min x y ≤ z.1 ∧ z.1 ≤ max x y ∧ z.2=(N : ℤ)+1 := by
    intro z hz
    exact hw z (w.support_toPath_subset_support hz)
  have hup : PD.FK.squareLattice.Adj (x,(N : ℤ)) (x,(N : ℤ)+1) := by
    change |x-x| + |(N : ℤ)-((N : ℤ)+1)| = 1
    norm_num
  have hdown : PD.FK.squareLattice.Adj (y,(N : ℤ)+1) (y,(N : ℤ)) := by
    change |y-y| + |((N : ℤ)+1)-(N : ℤ)| = 1
    norm_num
  have hyoutside : (y,(N : ℤ)) ∉ q.support := by
    intro h
    have hh := hqs _ h
    dsimp at hh
    omega
  have hxoutside : (x,(N : ℤ)) ∉ (q.concat hdown).support := by
    intro h
    rw [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at h
    rcases h with h | h
    · have hh := hqs _ h
      dsimp at hh
      omega
    · exact hxy (congrArg Prod.fst h)
  let p := (q.concat hdown).cons hup
  have hp : p.IsPath := (hq.concat hyoutside hdown).cons hxoutside
  refine ⟨p,hp,?_,?_,?_,?_⟩
  · simp only [p,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_concat]
    omega
  · intro z hz
    simp only [p,SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_concat,
      List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact ⟨min_le_left _ _,le_max_left _ _,le_rfl,by omega⟩
    · have hh := hqs z hz
      exact ⟨hh.1,hh.2.1,by omega,by omega⟩
    · exact ⟨min_le_right _ _,le_max_right _ _,le_rfl,by omega⟩
  · intro z hz hzN
    simp only [p,SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_concat,
      List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact Or.inl rfl
    · have hh := hqs z hz
      omega
    · exact Or.inr rfl
  · intro a b ha hb hab
    have hbound : ∀ z ∈ s(a,b), z.2 ≤ (N : ℤ) := by
      intro z hz
      rcases (Sym2.mem_iff').mp hz with rfl | rfl
      · exact ha
      · exact hb
    simp only [p,SimpleGraph.Walk.edges_cons,SimpleGraph.Walk.edges_concat,
      List.concat_eq_append,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false] at hab
    rcases hab with he | he | he
    · have hh := hbound (x,(N : ℤ)+1) (by rw [he]; exact (Sym2.mem_iff').mpr (Or.inr rfl))
      dsimp at hh
      omega
    · have hh := hqs a (q.fst_mem_support_of_mem_edges he)
      omega
    · have hh := hbound (y,(N : ℤ)+1) (by rw [he]; exact (Sym2.mem_iff').mpr (Or.inl rfl))
      dsimp at hh
      omega

end PottsContinuity.Push
