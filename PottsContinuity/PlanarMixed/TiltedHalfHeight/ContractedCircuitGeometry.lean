module

public import PottsContinuity.PlanarMixed.Lemma4Connectors.HullBoundaryCircuit
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.TopErasure

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- Nonzero enclosure forces a dual intersection above every enclosed
central primal vertex. -/
theorem closedWalk_meets_central_upper_ray {z : LatticeVertex}
    (p : squareLattice.Walk z z) (n : ℤ) (hn : rayIndex (0,n) p ≠ 0) :
    ∃ y : ℤ, n ≤ y ∧ s((-1,y),(0,y)) ∈ p.edges := by
  by_contra hno
  push Not at hno
  have hi (k : ℕ) : rayIndex (0,n+(k : ℤ)) p = rayIndex (0,n) p := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hd := rayIndex_vertical_difference 0 (n+(k:ℤ)) p (hno _ (by omega))
      simp only [sub_self] at hd
      have he : n+((k+1 : ℕ):ℤ) = (n+(k:ℤ))+1 := by omega
      rw [he]
      omega
  have hinf : (Set.range (fun k : ℕ => ((0 : ℤ),n+(k:ℤ)))).Infinite :=
    Set.infinite_range_of_injective (fun i j h => by
      have h' := congrArg Prod.snd h
      omega)
  apply hinf
  apply (finite_nonzero_rayIndex p).subset
  rintro _ ⟨k,rfl⟩
  change rayIndex (0,n+(k:ℤ)) p ≠ 0
  rw [hi]
  exact hn

/-- The same enclosed central vertex forces an intersection strictly below it. -/
theorem closedWalk_meets_central_lower_ray {z : LatticeVertex}
    (p : squareLattice.Walk z z) (n : ℤ) (hn : rayIndex (0,n) p ≠ 0) :
    ∃ y : ℤ, y < n ∧ s((-1,y),(0,y)) ∈ p.edges := by
  by_contra hno
  push Not at hno
  have hi (k : ℕ) : rayIndex (0,n-(k : ℤ)) p = rayIndex (0,n) p := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hd := rayIndex_vertical_difference 0 (n-((k+1:ℕ):ℤ)) p (hno _ (by omega))
      simp only [sub_self] at hd
      have he : n-((k+1:ℕ):ℤ)+1 = n-(k:ℤ) := by omega
      rw [he] at hd
      omega
  have hinf : (Set.range (fun k : ℕ => ((0 : ℤ),n-(k:ℤ)))).Infinite :=
    Set.infinite_range_of_injective (fun i j h => by
      have h' := congrArg Prod.snd h
      omega)
  apply hinf
  apply (finite_nonzero_rayIndex p).subset
  rintro _ ⟨k,rfl⟩
  change rayIndex (0,n-(k:ℤ)) p ≠ 0
  rw [hi]
  exact hn

/-- Every cell-boundary face lies below the top half-step whenever the whole
primal hull is disjoint from the wired top, on the nonpositive slope branch. -/
theorem cellBoundary_height_le_of_hull_not_top (N : ℕ) (t : ℝ) (ht : t ≤ 0)
    (C : Finset LatticeVertex) (hC : ∀ v ∈ C, tiltedHeight t v ≤ (N : ℝ)-1)
    {u v : LatticeVertex} (huv : (latticeCellBoundaryGraph (vertexCellBases C)).Adj u v) :
    tiltedHeight t u ≤ (N : ℝ)-1 ∧ tiltedHeight t v ≤ (N : ℝ)-1 := by
  obtain ⟨_,d,hd,hfaces⟩ := (latticeCellBoundaryGraph_adj_iff _ u v).mp huv
  have hf : d.faceBase true ∈ vertexCellBases C ∨ d.faceBase false ∈ vertexCellBases C := by
    by_cases h : d.faceBase true ∈ vertexCellBases C
    · exact Or.inl h
    · exact Or.inr (by by_contra hn; exact hfaces (propext (by simp [h,hn])))
  have hend : (u=d.source ∧ v=d.target) ∨ (u=d.target ∧ v=d.source) := by
    rcases Sym2.eq_iff.mp hd with h | h
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.2.symm,h.1.symm⟩
  rcases hf with hf | hf
  all_goals
    have hc := hC _ ((mem_vertexCellBases C _).mp hf)
    rcases d with ⟨⟨x,y⟩,axis⟩
    cases axis <;> rcases hend with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp only [LatticeBond.faceBase,LatticeBond.source,LatticeBond.target,
        tiltedHeight,Int.cast_add,Int.cast_sub,Int.cast_one,mul_add,mul_sub,mul_one] at hc ⊢ <;>
      constructor <;> linarith

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
