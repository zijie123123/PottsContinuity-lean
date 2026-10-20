module

public import PottsContinuity.PlanarMixed.FiniteSlit.LeftBarrierLoop
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK PD.Duality PlanarTopology PlanarMixed.FiniteSlit
noncomputable section

/-- Close a bottom-to-left-slit walk through the deleted seam and outside
on the left. Its index is one on the whole left wired arc and zero at every
later bottom start. The path may revisit the bottom or itself. -/
theorem exists_left_slit_barrier_with_support
    (M : ℕ) (x y a z : ℤ) (hM : 2 ≤ M) (hy : 0 < y)
    (hzy : y ≤ z) (hxa : x ≤ a)
    (p : PD.FK.squareLattice.Walk (a,0) (x-1,z))
    (hp : ∀ w ∈ p.support,
      x-(M:ℤ) < w.1 ∧ w.1 < x+(M:ℤ)-1 ∧ 0 ≤ w.2 ∧ w.2 < (M:ℤ)) :
    ∃ C : PD.FK.squareLattice.Walk (a,0) (a,0),
      (∀ e ∈ C.edges, e ∈ slitBarrierEdges M x y a p) ∧
      (∀ v : Vertex M x, v ∈ alpha M x → rayIndex v.val C = 1) ∧
      (∀ b : ℤ, a < b → rayIndex (b,0) C = 0) ∧
      (∀ w ∈ C.support,
        x-(M:ℤ) ≤ w.1 → w.1 ≤ x+(M:ℤ)-1 → 0 ≤ w.2 → w.2 ≤ (M:ℤ) →
        w ∈ p.support ∨ (w.1=x-1 ∧ z ≤ w.2)) := by
  have hzM := (hp _ p.end_mem_support).2.2.2
  have ha := hp _ p.start_mem_support
  obtain ⟨R,hR⟩ := vertical_walk_between (x-1) z ((M:ℤ)+1)
  obtain ⟨T,hT⟩ := horizontal_walk_between (x-1) (x-(M:ℤ)-1) ((M:ℤ)+1)
  obtain ⟨D,hD⟩ := vertical_walk_between (x-(M:ℤ)-1) ((M:ℤ)+1) (-1)
  obtain ⟨B,hB⟩ := horizontal_walk_between (x-(M:ℤ)-1) a (-1)
  have hU : PD.FK.squareLattice.Adj (a,-1) (a,0) := by
    rw [PD.FK.squareLattice_adj_iff]; norm_num
  let C := p.append (R.append (T.append (D.append (B.append hU.toWalk))))
  have hallowed : ∀ e ∈ C.edges, e ∈ slitBarrierEdges M x y a p := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    simp only [C,SimpleGraph.Walk.edges_append,List.mem_append] at he
    rcases he with he | he | he | he | he | he
    · exact Or.inl he
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inl ?_⟩))
      have hu := hR _ (R.fst_mem_support_of_mem_edges he)
      have hv := hR _ (R.snd_mem_support_of_mem_edges he)
      rw [min_eq_left (by omega : z ≤ (M:ℤ)+1)] at hu hv
      exact ⟨hu.1,hv.1,by omega,by omega⟩
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inr (Or.inr (Or.inl ?_))⟩))
      have hu := hT _ (T.fst_mem_support_of_mem_edges he)
      have hv := hT _ (T.snd_mem_support_of_mem_edges he)
      exact ⟨by omega,by omega⟩
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩))
      have hu := hD _ (D.fst_mem_support_of_mem_edges he)
      have hv := hD _ (D.snd_mem_support_of_mem_edges he)
      exact ⟨by omega,by omega⟩
    · refine Or.inr (Or.inr (Or.inr ⟨_,_,rfl,Or.inr (Or.inl ?_)⟩))
      have hu := hB _ (B.fst_mem_support_of_mem_edges he)
      have hv := hB _ (B.snd_mem_support_of_mem_edges he)
      exact ⟨by omega,by omega⟩
    · apply Or.inr ∘ Or.inl
      simpa using he
  have hRidx (v : LatticeVertex) (hv : v.1 ≤ x-1) :
      rayIndex v R = (if z < v.2 then 1 else 0) -
        (if (M:ℤ)+1 < v.2 then 1 else 0) := by
    apply rayIndex_left_telescope
    intro w hw
    have hh := (hR w hw).1
    omega
  have hDidx (v : LatticeVertex) (hv : x-(M:ℤ) ≤ v.1) : rayIndex v D = 0 := by
    apply rayIndex_zero_of_right
    intro w hw
    have hh := (hD w hw).1
    omega
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
  have hbottom (b : ℤ) (hb : x-(M:ℤ) ≤ b) :
      rayIndex (b,0) C = if b ≤ a then 1 else 0 := by
    have hp0 : rayIndex (b,0) p = 0 := by
      apply rayIndex_zero_of_level (b,0) p 0
      intro w hw
      exact ite_eq_right (by have := (hp w hw).2.2.1; dsimp; omega)
    have hR0 : rayIndex (b,0) R = 0 := by
      apply rayIndex_zero_of_level (b,0) R 0
      intro w hw
      have hh := (hR w hw).2.1
      rw [min_eq_left (by omega : z ≤ (M:ℤ)+1)] at hh
      exact ite_eq_right (by dsimp; omega)
    simp only [C,rayIndex_append,hp0,hR0,hDidx (b,0) hb,
      hTidx (b,0) (by dsimp; omega),hBidx (b,0) (by dsimp; omega),
      rayIndex,rayStep]
    simp
  refine ⟨C,hallowed,?_,?_,?_⟩
  · intro v hv
    have hvb := (mem_rectangle_iff M x (by omega) v.val).mp v.property
    rcases hv with ⟨hv0,hvx⟩ | hvx | ⟨hvM,hvx⟩
    · have he : v.val = (v.val.1,0) := Prod.ext rfl hv0
      rw [he,hbottom _ hvb.1,ite_eq_left (by omega)]
    · have hpL := rayIndex_left_telescope v.val p (by
        intro w hw; have := (hp w hw).1; omega)
      simp only [C,rayIndex_append,hpL,hRidx v.val (by omega),hDidx v.val hvb.1,
        hTidx v.val hvb.2.2.2,hBidx v.val hvb.2.2.1,rayIndex,rayStep]
      simp only [ite_eq_right (by omega : ¬ (M:ℤ)+1 < v.val.2),
        ite_eq_left (by omega : (-1:ℤ) < v.val.2),ite_eq_left (by omega : v.val.1 ≤ a)]
      omega
    · have hpM : rayIndex v.val p = 0 := by
        apply rayIndex_zero_of_level v.val p 1
        intro w hw
        exact ite_eq_left (by have := (hp w hw).2.2.2; omega)
      simp only [C,rayIndex_append,hpM,hRidx v.val hvx,hDidx v.val hvb.1,
        hTidx v.val hvb.2.2.2,hBidx v.val hvb.2.2.1,rayIndex,rayStep]
      simp [hvM,show z < (M:ℤ) by omega,
        show (-1:ℤ) < M by omega,show 0 < M by omega]
  · intro b hb
    rw [hbottom _ (by omega),ite_eq_right (by omega)]

  · intro w hw hwl hwr hw0 hwM
    simp only [C,SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw | hw | hw | hw | hw
    · exact Or.inl hw
    · have hr := hR w hw
      exact Or.inr ⟨hr.1,by omega⟩
    · have ht := (hT w hw).2.2
      omega
    · have hd := (hD w hw).1
      omega
    · have hb := (hB w hw).2.2
      omega
    · have hu : w=(a,-1) ∨ w=(a,0) := by simpa using hw
      rcases hu with rfl | rfl
      · omega
      · exact Or.inl p.start_mem_support

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
