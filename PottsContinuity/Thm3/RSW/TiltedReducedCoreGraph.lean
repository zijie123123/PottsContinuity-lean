module

public import PottsContinuity.Thm3.RSW.TiltedReducedCoreEmbedding

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality DualityExt Thm3.Prop4
noncomputable section

 theorem reduced_source_bond_source_window (N L : ℕ) (t : ℝ)
    (e : (tiltedWindowReducedGraph N L t).edgeSet) :
    (tiltedReducedFiniteSourceBond N L t e).source ∈ tiltedWindow N L t := by
  have hz : (tiltedReducedFiniteSourceBond N L t e).source ∈
      Sym2.map (fun z => z.val) e.val := by
    rw [← tiltedReducedFiniteSourceBond_pair]
    simp [LatticeBond.toSym2]
  obtain ⟨z,hz,heq⟩ := Sym2.mem_map.mp hz
  exact heq ▸ z.property

 theorem reduced_crossed_endpoints_box (N L M : ℕ) (t : ℝ) (hM : L+N+3 ≤ M)
    (b : LatticeBond) (hb : |b.base.1| ≤ (L:ℤ) ∧ |b.base.2| ≤ (L:ℤ)) :
    (tiltedStripReducedCrossedBond N t b).source ∈ box M ∧
    (tiltedStripReducedCrossedBond N t b).target ∈ box M := by
  rw [Foundations.mem_box_iff_abs_le,Foundations.mem_box_iff_abs_le]
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> by_cases hp : 0 < t
  all_goals
    simp only [tiltedStripReducedCrossedBond,hp,ite_true,ite_false,
      LatticeBond.source,LatticeBond.target] at hb ⊢
    simp only [abs_le] at hb
    simp only [abs_le]
    omega

/-- The crossed image of a retained core edge is an actual retained source
edge of a sufficiently large native finite window. -/
def tiltedReducedCoreCrossedEdge (N L M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (e : (tiltedWindowReducedGraph N L t).edgeSet) :
    (tiltedWindowReducedGraph N M t).edgeSet := by
  classical
  let b := tiltedReducedFiniteSourceBond N L t e
  have hb := tiltedReducedFiniteSourceBond_retained N L t e
  let br : tiltedStripReducedCarrier N t := ⟨⟨b,hb.1,hb.2.1⟩,hb.2.2⟩
  have hcross := tiltedStripReducedCrossedBond_mem N t ht br
  have hwindow := reduced_source_bond_source_window N L t e
  have hbase : |b.base.1| ≤ (L:ℤ) ∧ |b.base.2| ≤ (L:ℤ) :=
    (Foundations.mem_box_iff_abs_le L b.source).mp ((mem_tiltedWindow N L t b.source).mp hwindow).1
  have hbox := reduced_crossed_endpoints_box N L M t hM b hbase
  let u : (tiltedWindow N M t : Set (ℤ × ℤ)) :=
    ⟨(tiltedStripReducedCrossedBond N t b).source,
      (mem_tiltedWindow N M t _).mpr ⟨hbox.1,hcross.1⟩⟩
  let v : (tiltedWindow N M t : Set (ℤ × ℤ)) :=
    ⟨(tiltedStripReducedCrossedBond N t b).target,
      (mem_tiltedWindow N M t _).mpr ⟨hbox.2,hcross.2.1⟩⟩
  let G := squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))
  let e0 : G.edgeSet := ⟨s(u,v),(tiltedStripReducedCrossedBond N t b).adjacent⟩
  have hnot : e0 ∉ tiltedWindowTopTopEdges N M t := by
    intro he
    simp only [tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he
    exact hcross.2.2 ⟨he u (by simp [e0]),he v (by simp [e0])⟩
  exact (edgeRestrictionEdgeEquiv G (tiltedWindowTopTopEdges N M t)).symm ⟨e0,hnot⟩

/-- No original edge is changed by the core lift beyond the announced
crossed-bond map. -/
theorem tiltedReducedCoreCrossedEdge_pair (N L M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (e : (tiltedWindowReducedGraph N L t).edgeSet) :
    Sym2.map (fun z => z.val) (tiltedReducedCoreCrossedEdge N L M t ht hM e).val =
      (tiltedStripReducedCrossedBond N t (tiltedReducedFiniteSourceBond N L t e)).toSym2 := rfl

/-- The finite host normalization of the lifted edge is exactly the
crossed original bond, with its axis exchanged. -/
theorem tiltedReducedCoreCrossedEdge_sourceBond (N L M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (e : (tiltedWindowReducedGraph N L t).edgeSet) :
    tiltedReducedFiniteSourceBond N M t (tiltedReducedCoreCrossedEdge N L M t ht hM e) =
      tiltedStripReducedCrossedBond N t (tiltedReducedFiniteSourceBond N L t e) := by
  apply LatticeBond.toSym2_injective
  rw [tiltedReducedFiniteSourceBond_pair,tiltedReducedCoreCrossedEdge_pair]

/-- Every retained core edge occurs in the genuine finite dual graph under
the full-carrier core embedding; isolated top vertices cause no exception. -/
theorem tiltedReducedCoreDual_map_le (N L M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M) :
    (tiltedWindowReducedGraph N L t).map (tiltedReducedCoreDualEmbedding N L M t hM) ≤
      rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t) := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  let e : (tiltedWindowReducedGraph N L t).edgeSet :=
    ⟨s(x,y),(tiltedWindowReducedGraph N L t).mem_edgeSet.mpr hxy⟩
  let g := tiltedReducedCoreCrossedEdge N L M t ht hM e
  let d := tiltedReducedFiniteDualEdge N M t g
  have hd := tiltedReducedFiniteDualEdge_crossed_pair N M t g
  rw [tiltedReducedCoreCrossedEdge_sourceBond] at hd
  rw [tiltedStripReducedCrossedBond_involutive] at hd
  have hother : Sym2.map (fun z => tiltedStripReducedDualVertex N t z.val)
      (s(tiltedReducedCoreDualEmbedding N L M t hM x,
         tiltedReducedCoreDualEmbedding N L M t hM y)) =
      (tiltedReducedFiniteSourceBond N L t e).toSym2 := by
    change s(tiltedStripReducedDualVertex N t (tiltedReducedCoreDualEmbedding N L M t hM x).val,
      tiltedStripReducedDualVertex N t (tiltedReducedCoreDualEmbedding N L M t hM y).val) = _
    rw [tiltedReducedCoreDualEmbedding_replay,tiltedReducedCoreDualEmbedding_replay,
      tiltedReducedFiniteSourceBond_pair]
    rfl
  have hinj : Function.Injective (fun z : RectangleDualVertex
      (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) =>
        tiltedStripReducedDualVertex N t z.val) := by
    intro z w heq
    apply Subtype.ext
    apply Prod.ext
    · have hx := congrArg Prod.fst heq
      dsimp [tiltedStripReducedDualVertex] at hx
      omega
    · have hy := congrArg Prod.snd heq
      dsimp [tiltedStripReducedDualVertex] at hy
      omega
  have hpair := (Sym2.map.injective hinj) (hd.trans hother.symm)
  change s(tiltedReducedCoreDualEmbedding N L M t hM x,
    tiltedReducedCoreDualEmbedding N L M t hM y) ∈
      (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)).edgeSet
  rw [← hpair]
  exact d.property

end
end PottsContinuity.RSW
