module

public import PottsContinuity.Thm4Side.DeterministicReveals
public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain

@[expose] public section

namespace PottsContinuity.Thm4Side

open PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem slitResidual_edge_endpoints
    (m : ℕ) (e : (slitBoxGraph (16 * m)).edgeSet) :
    ∃ u v : SlitBoxVertex (16 * m), s(u, v) = e.val ∧
      (slitBoxGraph (16 * m)).Adj u v := by
  let p := e.val.out
  have hp : s(p.1, p.2) = e.val := Quot.out_eq _
  refine ⟨p.1, p.2, hp, ?_⟩
  apply (slitBoxGraph (16 * m)).mem_edgeSet.mp
  rw [hp]
  exact e.property

private theorem slitResidual_adjacent_x_bounds
    (m : ℕ) {u v : SlitBoxVertex (16 * m)}
    (h : (slitBoxGraph (16 * m)).Adj u v) :
    u.val.1 ≤ v.val.1 + 1 ∧ v.val.1 ≤ u.val.1 + 1 := by
  have hsq := ((slitBoxGraph_adj_iff (16 * m) u v).mp h).1
  rcases (PottsContinuity.FKC.squareLattice_adj_iff u.val v.val).mp hsq with
    ⟨hx | hx, _⟩ | ⟨_, _⟩ <;> omega

/-- The right residual edge set consists exactly of bonds whose two endpoints
are on or to the right of the cut. -/
theorem slitRightHalfReveal_complement_edge_iff (m : ℕ)
    (e : (slitBoxGraph (16 * m)).edgeSet) :
    e ∉ slitRightHalfRevealEdges m ↔
      ∀ v ∈ e.val, (m : ℤ) ≤ v.val.1 := by
  obtain ⟨u, v, hev, hadj⟩ := slitResidual_edge_endpoints m e
  have huMem : u ∈ e.val := by
    rw [← hev]
    exact (Sym2.mem_iff').mpr (Or.inl rfl)
  have hvMem : v ∈ e.val := by
    rw [← hev]
    exact (Sym2.mem_iff').mpr (Or.inr rfl)
  have hstep := slitResidual_adjacent_x_bounds m hadj
  have hpair (z : SlitBoxVertex (16 * m)) (hz : z ∈ e.val) :
      z = u ∨ z = v := by
    have hz' : z ∈ s(u, v) := by rw [hev]; exact hz
    exact (Sym2.mem_iff').mp hz'
  constructor
  · intro hnot z hz
    rcases hpair z hz with hzu | hzv
    · by_contra hbound
      have huNot : ¬ (m : ℤ) ≤ u.val.1 := by simpa [hzu] using hbound
      have huLt : u.val.1 < (m : ℤ) := lt_of_not_ge huNot
      have hvLe : v.val.1 ≤ (m : ℤ) := by omega
      have hleft : ∀ z ∈ e.val, z.val.1 ≤ (m : ℤ) := by
        intro z hz
        rcases hpair z hz with hzu' | hzv'
        · rw [hzu']
          exact le_of_lt huLt
        · rw [hzv']
          exact hvLe
      have hnotAll : ¬ ∀ z ∈ e.val, z.val.1 = (m : ℤ) := by
        intro hAll
        have hEq := hAll u huMem
        omega
      apply hnot
      simp only [slitRightHalfRevealEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hleft, hnotAll⟩
    · by_contra hbound
      have hvNot : ¬ (m : ℤ) ≤ v.val.1 := by simpa [hzv] using hbound
      have hvLt : v.val.1 < (m : ℤ) := lt_of_not_ge hvNot
      have huLe : u.val.1 ≤ (m : ℤ) := by omega
      have hleft : ∀ z ∈ e.val, z.val.1 ≤ (m : ℤ) := by
        intro z hz
        rcases hpair z hz with hzu' | hzv'
        · rw [hzu']
          exact huLe
        · rw [hzv']
          exact le_of_lt hvLt
      have hnotAll : ¬ ∀ z ∈ e.val, z.val.1 = (m : ℤ) := by
        intro hAll
        have hEq := hAll v hvMem
        omega
      apply hnot
      simp only [slitRightHalfRevealEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hleft, hnotAll⟩
  · intro hright hmem
    have hmem' : (∀ z ∈ e.val, z.val.1 ≤ (m : ℤ)) ∧
        ¬ ∀ z ∈ e.val, z.val.1 = (m : ℤ) := by
      simpa only [slitRightHalfRevealEdges, Finset.mem_filter,
        Finset.mem_univ, true_and] using hmem
    apply hmem'.2
    intro z hz
    have hge := hright z hz
    exact le_antisymm (hmem'.1 z hz) hge

end
end PottsContinuity.Thm4Side
