module

public import PottsContinuity.PlanarMixed.FiniteSlit.ActiveCarrier

/-! Exact isolated faces of the reflected finite carrier. The outer left
column and the unmarked bottom vertices carry no sampled dual edges. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12
noncomputable section

/-- Every sampled reflected endpoint is strictly right of the left outer
column; a bottom endpoint belongs to the correct left bottom half. -/
theorem activeBond_reflected_boundary_bounds (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (b : LatticeBond) (hb : ActiveBond M x y b) :
    (x-(M : ℤ) < (slitReflectedBond x b).source.1 ∧
      ((slitReflectedBond x b).source.2 = 0 → (slitReflectedBond x b).source.1 ≤ x-1)) ∧
    (x-(M : ℤ) < (slitReflectedBond x b).target.1 ∧
      ((slitReflectedBond x b).target.2 = 0 → (slitReflectedBond x b).target.1 ≤ x-1)) := by
  obtain ⟨hs,ht,_,hn⟩ := hb
  have hsb := (mem_rectangle_iff M x (by omega) b.source).mp hs
  have htb := (mem_rectangle_iff M x (by omega) b.target).mp ht
  rcases b with ⟨⟨a,k⟩,ax⟩
  cases ax
  · simp only [LatticeBond.source,LatticeBond.target] at hsb htb
    have hk : k = 0 → x ≤ a := by
      intro hk
      by_contra ha
      apply hn
      refine ⟨hs,ht,Or.inl ⟨?_,?_⟩⟩
      all_goals
        change (_ = 0 ∧ _ ≤ x) ∨ _
        apply Or.inl
        simp only [LatticeBond.source,LatticeBond.target]
        omega
    simp only [slitReflectedBond,LatticeBond.source,LatticeBond.target]
    constructor <;> constructor <;> omega
  · simp only [LatticeBond.source,LatticeBond.target] at hsb htb
    have ha : a ≠ x+(M : ℤ)-1 := by
      intro ha
      apply hn
      refine ⟨hs,ht,Or.inr ⟨?_,?_⟩⟩
      all_goals
        apply Or.inl
        exact ha
    simp only [slitReflectedBond,LatticeBond.source,LatticeBond.target]
    constructor <;> constructor <;> omega

/-- Coordinate restrictions on both endpoints of every actual sampled dual edge. -/
theorem dualGraph_adj_boundary_bounds (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (u v : Vertex M x) (huv : (dualGraph M x y).Adj u v) :
    (x-(M : ℤ) < u.val.1 ∧ (u.val.2 = 0 → u.val.1 ≤ x-1)) ∧
    (x-(M : ℤ) < v.val.1 ∧ (v.val.2 = 0 → v.val.1 ≤ x-1)) := by
  obtain ⟨⟨b,hb,hpair⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
  have h := activeBond_reflected_boundary_bounds M x y hM b hb
  rcases Sym2.eq_iff.mp hpair with he | he
  · simpa only [he.1,he.2,Function.Embedding.subtype_apply] using h
  · simpa only [he.1,he.2,Function.Embedding.subtype_apply] using h.symm

/-- The entire target left outer column is isolated, including its corners. -/
theorem dualGraph_left_column_isolated (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (u : Vertex M x) (hu : u.val.1 = x-(M : ℤ)) :
    ∀ v, ¬ (dualGraph M x y).Adj u v := by
  intro v h
  have hbound := (dualGraph_adj_boundary_bounds M x y hM u v h).1.1
  omega

/-- Every bottom vertex outside B' is isolated. Wiring it at the rectangle
exterior cannot create an additional sampled edge or an actual marked path. -/
theorem dualGraph_unmarked_bottom_isolated (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (u : Vertex M x) (hu : u.val.2 = 0) (hB : u ∉ dualBottom M x) :
    ∀ v, ¬ (dualGraph M x y).Adj u v := by
  intro v h
  have hb := (dualGraph_adj_boundary_bounds M x y hM u v h).1
  apply hB
  change u.val.2 = 0 ∧ x-(M : ℤ)+1 ≤ u.val.1 ∧ u.val.1 ≤ x-1
  exact ⟨hu,by omega,hb.2 hu⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
