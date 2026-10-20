module

public import PottsContinuity.Thm3.Push.IntervalArmDualPorts
public import PottsContinuity.Thm3.Push.BondFaceIndex
public import PottsContinuity.PlanarMixed.FiniteSlit.LeftBarrierLoop

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK PD.FK.Medial PD.Duality Push PlanarMixed.FiniteSlit
noncomputable section

/-- Across the empty columns to the left of the source, a slit barrier has
unchanged row index up to the reference boundary. -/
theorem slitBarrier_left_row_index_eq_boundary
    (M : ℕ) (x y a t Y : ℤ) (hx : 1 ≤ x) (hxa : x ≤ a)
    (hleft : x-(M:ℤ) ≤ 0) (hY0 : 0 ≤ Y) (hYM : Y ≤ (M:ℤ))
    (q : squareLattice.Walk (a,0) (x-1,t))
    (hq : ∀ z ∈ q.support, 0 ≤ z.1)
    (L : squareLattice.Walk (a,0) (a,0))
    (hallowed : ∀ e ∈ L.edges, e ∈ slitBarrierEdges M x y a q) :
    rayIndex (0,Y) L=rayIndex (x-(M:ℤ),Y) L := by
  have hstep (i : ℤ) (hi : x-(M:ℤ) ≤ i) (hi0 : i<0) :
      rayIndex (i,Y) L=rayIndex (i+1,Y) L := by
    apply rayIndex_horizontal_invariant i Y L
    intro he
    rcases hallowed _ he with hq' | hroot | ⟨htip,_⟩ | ⟨u,v,huv,hout⟩
    · have hh := hq _ (q.fst_mem_support_of_mem_edges hq')
      dsimp at hh
      omega
    · rcases Sym2.eq_iff.mp hroot with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have h1x := congrArg Prod.fst h1 <;> have h2x := congrArg Prod.fst h2 <;> omega
    · rcases Sym2.eq_iff.mp htip with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have h1x := congrArg Prod.fst h1 <;> have h2x := congrArg Prod.fst h2 <;> omega
    · rcases Sym2.eq_iff.mp huv with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have h1x := congrArg Prod.fst h1 <;> have h2x := congrArg Prod.fst h2 <;>
        have h1y := congrArg Prod.snd h1 <;> have h2y := congrArg Prod.snd h2 <;>
        rcases hout with hh | hh | hh | hh | hh <;> dsimp at * <;> omega
  have hind : ∀ k : ℕ, x-(M:ℤ)+(k:ℤ) ≤ 0 →
      rayIndex (x-(M:ℤ)+(k:ℤ),Y) L=rayIndex (x-(M:ℤ),Y) L := by
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero,add_zero,implies_true]
    | succ k ih =>
      intro hk
      have hh := (hstep (x-(M:ℤ)+(k:ℤ)) (by omega) (by omega)).symm.trans (ih (by omega))
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hh
  have hz : x-(M:ℤ)+(((M:ℤ)-x).toNat:ℤ)=0 := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hh := hind ((M:ℤ)-x).toNat (by rw [hz])
  simpa only [hz] using hh

/-- All raw left exploration ports carry alpha's index, including the
one-unit shift from face bases to the integer face-index marks. -/
theorem leftSlitBarrier_interval_left_ports_index_one
    (N M : ℕ) (x y a t : ℤ) (hM : 2 ≤ M) (hx : 1 ≤ x) (hxa : x ≤ a)
    (hleft : x-(M:ℤ) ≤ 0) (hright : x ≤ x+(M:ℤ)-1) (hNM : N+1 ≤ M)
    (q : squareLattice.Walk (a,0) (x-1,t)) (hq : ∀ z ∈ q.support, 0 ≤ z.1)
    (L : squareLattice.Walk (a,0) (a,0))
    (hallowed : ∀ e ∈ L.edges, e ∈ slitBarrierEdges M x y a q)
    (hα : ∀ v : Vertex M x, v ∈ alpha M x → rayIndex v.val L=1)
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmLeftDualPorts N x) :
    rayIndex (faceIndexMark v.val) L=1 := by
  have hb := (PD.FK.mem_latticeRectangle _ _ _ _).mp v.property
  change ((-1:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ -1+((N+1:ℕ):ℤ)) ∧
    ((-1:ℤ) ≤ v.val.2 ∧ v.val.2 ≤ -1+((N+1:ℕ):ℤ)) at hb
  rcases (mem_intervalArmLeftDualPorts N x v).mp hv with hvx | ⟨hvy,hvx⟩
  · let u : Vertex M x := ⟨(x-(M:ℤ),v.val.2+1),
      (mem_rectangle_iff M x (by omega) _).mpr ⟨le_rfl,by omega,by omega,by omega⟩⟩
    have hi := slitBarrier_left_row_index_eq_boundary M x y a t (v.val.2+1) hx hxa hleft
      (by omega) (by omega) q hq L hallowed
    have hu := hα u (Or.inr (Or.inl rfl))
    have hi' : rayIndex (faceIndexMark v.val) L=rayIndex u.val L := by
      simpa only [faceIndexMark,hvx,neg_add_cancel] using hi
    exact hi'.trans hu
  · let u : Vertex M x := ⟨(v.val.1+1,0),
      (mem_rectangle_iff M x (by omega) _).mpr ⟨by omega,by omega,by omega,by omega⟩⟩
    have hu := hα u (Or.inl ⟨rfl,by dsimp [u]; omega⟩)
    simpa only [faceIndexMark,hvy,neg_add_cancel] using hu

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
