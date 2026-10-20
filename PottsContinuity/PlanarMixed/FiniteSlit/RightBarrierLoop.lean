module

public import PottsContinuity.PlanarMixed.FiniteSlit.LeftBarrierLoop

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.Duality PlanarTopology
noncomputable section

/-- The right crosscut closes across the tip, along the deleted seam and
outside on the right. Its index separates the right wired arc from every
earlier bottom start, even when the original walk has repeated contacts. -/
theorem exists_right_slit_barrier
    (M : ℕ) (x y b : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hxb : x < b)
    (q : PD.FK.squareLattice.Walk (b,0) (x,y))
    (hq : ∀ w ∈ q.support,
      x ≤ w.1 ∧ w.1 < x+(M:ℤ)-1 ∧ 0 ≤ w.2 ∧ w.2 < (M:ℤ)) :
    ∃ C : PD.FK.squareLattice.Walk (b,0) (b,0),
      (∀ e ∈ C.edges, e ∈ slitBarrierEdges M x y b q) ∧
      (∀ v : Vertex M x, v ∈ alpha M x → rayIndex v.val C = 0) ∧
      (∀ v : Vertex M x, v ∈ beta M x y → v.val ∉ q.support → rayIndex v.val C = -1) ∧
      (∀ a : ℤ, a < b → rayIndex (a,0) C = 0) := by
  have hyM := (hq _ q.end_mem_support).2.2.2
  have hb := hq _ q.start_mem_support
  have htip : PD.FK.squareLattice.Adj (x,y) (x-1,y) := by
    rw [PD.FK.squareLattice_adj_iff]; dsimp; omega
  obtain ⟨R,hR⟩ := vertical_walk_between (x-1) y ((M:ℤ)+1)
  obtain ⟨T,hT⟩ := horizontal_walk_between (x-1) (x+(M:ℤ)) ((M:ℤ)+1)
  obtain ⟨D,hD⟩ := vertical_walk_between (x+(M:ℤ)) ((M:ℤ)+1) (-1)
  obtain ⟨B,hB⟩ := horizontal_walk_between (x+(M:ℤ)) b (-1)
  have hU : PD.FK.squareLattice.Adj (b,-1) (b,0) := by
    rw [PD.FK.squareLattice_adj_iff]; norm_num
  let C := q.append (htip.toWalk.append (R.append (T.append (D.append (B.append hU.toWalk)))))
  have hallowed : ∀ e ∈ C.edges, e ∈ slitBarrierEdges M x y b q := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    simp only [C,SimpleGraph.Walk.edges_append,List.mem_append] at he
    rcases he with he | he | he | he | he | he | he
    · exact Or.inl he
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      refine ⟨?_,q.end_mem_support⟩
      have he' : s(u,v) = s((x,y),(x-1,y)) := by simpa using he
      exact he'.trans Sym2.eq_swap
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inl ?_⟩))
      have hu := hR _ (R.fst_mem_support_of_mem_edges he)
      have hv := hR _ (R.snd_mem_support_of_mem_edges he)
      rw [min_eq_left (by omega : y ≤ (M:ℤ)+1)] at hu hv
      exact ⟨hu.1,hv.1,hu.2.1,hv.2.1⟩
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inr (Or.inr (Or.inl ?_))⟩))
      have hu := hT _ (T.fst_mem_support_of_mem_edges he)
      have hv := hT _ (T.snd_mem_support_of_mem_edges he)
      exact ⟨by omega,by omega⟩
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩))
      have hu := hD _ (D.fst_mem_support_of_mem_edges he)
      have hv := hD _ (D.snd_mem_support_of_mem_edges he)
      exact ⟨by omega,by omega⟩
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inr (Or.inl ?_)⟩))
      have hu := hB _ (B.fst_mem_support_of_mem_edges he)
      have hv := hB _ (B.snd_mem_support_of_mem_edges he)
      exact ⟨by omega,by omega⟩
    · apply Or.inr ∘ Or.inl
      simpa using he
  have htipIdx (v : LatticeVertex) : rayIndex v htip.toWalk = 0 := by
    simp [rayIndex,rayStep]
  have hRidx (v : LatticeVertex) (hv : x ≤ v.1) : rayIndex v R = 0 := by
    apply rayIndex_zero_of_right
    intro w hw
    have hh := (hR w hw).1
    omega
  have hDidx (v : LatticeVertex) (hv : v.1 ≤ x+(M:ℤ))
      (hv0 : 0 ≤ v.2) (hvM : v.2 ≤ (M:ℤ)) : rayIndex v D = -1 := by
    rw [rayIndex_left_telescope v D (by
      intro w hw; have := (hD w hw).1; omega)]
    simp only [ite_eq_right (by omega : ¬ (M:ℤ)+1 < v.2),
      ite_eq_left (by omega : (-1:ℤ) < v.2)]
    norm_num
  have hTidx (v : LatticeVertex) (hv : v.2 ≤ (M:ℤ)) : rayIndex v T = 0 := by
    apply rayIndex_zero_of_level v T 0
    intro w hw
    have hh := (hT w hw).2.2
    exact ite_eq_right (by omega)
  have hBidx (v : LatticeVertex) (hv : 0 ≤ v.2) : rayIndex v B = 0 := by
    apply rayIndex_zero_of_level v B 1
    intro w hw
    have hh := (hB w hw).2.2
    exact ite_eq_left (by omega)
  have hRleft (v : LatticeVertex) (hv : v.1 ≤ x-1) :
      rayIndex v R = (if y < v.2 then 1 else 0) -
        (if (M:ℤ)+1 < v.2 then 1 else 0) := by
    apply rayIndex_left_telescope
    intro w hw
    have := (hR w hw).1
    omega
  refine ⟨C,hallowed,?_,?_,?_⟩
  · intro v hv
    have hvb := (mem_rectangle_iff M x (by omega) v.val).mp v.property
    rcases hv with ⟨hv0,hvx⟩ | hvx | ⟨hvM,hvx⟩
    · have hq0 : rayIndex v.val q = 0 := by
        apply rayIndex_zero_of_level v.val q 0
        intro w hw
        exact ite_eq_right (by have := (hq w hw).2.2.1; omega)
      have hR0 : rayIndex v.val R = 0 := by
        apply rayIndex_zero_of_level v.val R 0
        intro w hw
        have hh := (hR w hw).2.1
        rw [min_eq_left (by omega : y ≤ (M:ℤ)+1)] at hh
        exact ite_eq_right (by omega)
      simp only [C,rayIndex_append,hq0,hR0,
        hTidx v.val hvb.2.2.2,hDidx v.val (by omega) hvb.2.2.1 hvb.2.2.2,
        hBidx v.val hvb.2.2.1,rayIndex,rayStep]
      simp [hv0,show v.val.1 ≤ b by omega]
    · have hqL := rayIndex_left_telescope v.val q (by
        intro w hw; have := (hq w hw).1; omega)
      simp only [C,rayIndex_append,hqL,hRleft v.val (by omega),
        hTidx v.val hvb.2.2.2,hDidx v.val (by omega) hvb.2.2.1 hvb.2.2.2,
        hBidx v.val hvb.2.2.1,rayIndex,rayStep]
      simp only [ite_eq_right (by omega : ¬ (M:ℤ)+1 < v.val.2),
        ite_eq_left (by omega : (-1:ℤ) < v.val.2),ite_eq_left (by omega : v.val.1 ≤ b)]
      omega
    · have hqM : rayIndex v.val q = 0 := by
        apply rayIndex_zero_of_level v.val q 1
        intro w hw
        exact ite_eq_left (by have := (hq w hw).2.2.2; omega)
      simp only [C,rayIndex_append,hqM,hRleft v.val hvx,
        hTidx v.val hvb.2.2.2,hDidx v.val (by omega) hvb.2.2.1 hvb.2.2.2,
        hBidx v.val hvb.2.2.1,rayIndex,rayStep]
      simp [hvM,show y < (M:ℤ) by omega,show 0 < M by omega,
        show (-1:ℤ) < M by omega]
  · intro v hv hnq
    have hvb := (mem_rectangle_iff M x (by omega) v.val).mp v.property
    have hvx : x ≤ v.val.1 := by
      rcases hv with h | h | h <;> omega
    have hqid : rayIndex v.val q = 0 := by
      rcases hv with hright | ⟨htop,_⟩ | ⟨hcol,hheight⟩
      · apply rayIndex_zero_of_right
        intro w hw
        have := (hq w hw).2.1
        omega
      · apply rayIndex_zero_of_level v.val q 1
        intro w hw
        exact ite_eq_left (by have := (hq w hw).2.2.2; omega)
      · have hne : y < v.val.2 := by
          by_contra h
          have he : v.val = (x,y) := Prod.ext hcol (by omega)
          exact hnq (he.symm ▸ q.end_mem_support)
        rw [rayIndex_left_telescope v.val q (by
          intro w hw; have := (hq w hw).1; omega)]
        simp only [ite_eq_left (by omega : (0:ℤ) < v.val.2),ite_eq_left hne,sub_self]
    have hUidx : rayIndex v.val hU.toWalk = 0 := by
      rcases hv with hright | ⟨htop,_⟩ | ⟨hcol,hheight⟩
      · simp [rayIndex,rayStep,show ¬ v.val.1 ≤ b by omega]
      · simp [rayIndex,rayStep,htop,show 0 < M by omega,show (-1:ℤ) < M by omega]
      · simp [rayIndex,rayStep,show (0:ℤ) < v.val.2 by omega,
          show (-1:ℤ) < v.val.2 by omega]
    simp only [C,rayIndex_append,hqid,htipIdx,hRidx v.val hvx,
      hTidx v.val hvb.2.2.2,hDidx v.val (by omega) hvb.2.2.1 hvb.2.2.2,
      hBidx v.val hvb.2.2.1,hUidx]
    norm_num
  · intro a hab
    have hq0 : rayIndex (a,0) q = 0 := by
      apply rayIndex_zero_of_level (a,0) q 0
      intro w hw
      exact ite_eq_right (by have := (hq w hw).2.2.1; dsimp; omega)
    have hR0 : rayIndex (a,0) R = 0 := by
      apply rayIndex_zero_of_level (a,0) R 0
      intro w hw
      have hh := (hR w hw).2.1
      rw [min_eq_left (by omega : y ≤ (M:ℤ)+1)] at hh
      exact ite_eq_right (by dsimp; omega)
    simp only [C,rayIndex_append,hq0,hR0,hTidx (a,0) (by dsimp; omega),
      hDidx (a,0) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega),
      hBidx (a,0) (by dsimp; omega),rayIndex,rayStep]
    simp [show a ≤ b by omega]

end
end PottsContinuity.PlanarMixed.FiniteSlit
