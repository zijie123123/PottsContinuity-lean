module

public import PottsContinuity.PlanarMixed.FiniteSlit.RightBarrierLoop

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PD.Duality PlanarMixed.FiniteSlit

/-- To the right of the root, a row missing the actual source-trace
crossing bonds has constant barrier index up to the right outer boundary. -/
theorem slitBarrier_row_index_eq_right_boundary_of_trace_gap
    (M : ℕ) (_hM : 2 ≤ M) (b y Y K : ℤ)
    (hY0 : 0 ≤ Y) (hYM : Y ≤ (M:ℤ)) (h2K : 2 < K) (hbK : b < K)
    (q : squareLattice.Walk (b,0) (2,y))
    (p : squareLattice.Walk (b,0) (b,0))
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M 2 y b q)
    (hgap : ∀ i : ℤ, K ≤ i → i ≤ (M:ℤ) → s((i,Y-1),(i,Y)) ∉ q.edges)
    (t : ℤ) (hKt : K ≤ t) (htM : t ≤ (M:ℤ)+1) :
    rayIndex (t,Y) p = rayIndex ((M:ℤ)+1,Y) p := by
  have hstep (i : ℤ) (hKi : K ≤ i) (hiM : i ≤ (M:ℤ)) :
      rayIndex (i,Y) p = rayIndex (i+1,Y) p := by
    apply rayIndex_horizontal_invariant i Y p
    intro he
    rcases hallowed _ he with hq | hroot | ⟨htip,_⟩ | ⟨u,v,huv,hout⟩
    · exact hgap i hKi hiM hq
    · rcases Sym2.eq_iff.mp hroot with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hx1 := congrArg Prod.fst h1 <;> have hx2 := congrArg Prod.fst h2 <;> omega
    · rcases Sym2.eq_iff.mp htip with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hx1 := congrArg Prod.fst h1 <;> have hx2 := congrArg Prod.fst h2 <;> omega
    · rcases Sym2.eq_iff.mp huv with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hx1 := congrArg Prod.fst h1 <;> have hx2 := congrArg Prod.fst h2 <;>
        have hy1 := congrArg Prod.snd h1 <;> have hy2 := congrArg Prod.snd h2 <;>
        rcases hout with hcol | hbottom | htop | hleft | hright <;> omega
  have hk : ∀ k : ℕ, t+(k:ℤ) ≤ (M:ℤ)+1 →
      rayIndex (t+(k:ℤ),Y) p = rayIndex (t,Y) p := by
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero,add_zero,implies_true]
    | succ k ih =>
      intro hk
      have hi : t+(k:ℤ) ≤ (M:ℤ) := by omega
      have hs := hstep (t+(k:ℤ)) (by omega) hi
      have hh := hs.symm.trans (ih (by omega))
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hh
  have hcast : t+(((M:ℤ)+1-t).toNat:ℤ) = (M:ℤ)+1 := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hh := hk ((M:ℤ)+1-t).toNat (by rw [hcast])
  rw [hcast] at hh
  exact hh.symm

/-- The bottom row to the right of the starting interval always has the
right-boundary index: the actual source walk stays at nonnegative height. -/
theorem slitBarrier_bottom_right_index_eq_boundary
    (M : ℕ) (hM : 2 ≤ M) (b y t : ℤ) (h2b : 2 < b)
    (hbt : b < t) (htM : t ≤ (M:ℤ)+1)
    (q : squareLattice.Walk (b,0) (2,y))
    (hq : ∀ z ∈ q.support, 0 ≤ z.2)
    (p : squareLattice.Walk (b,0) (b,0))
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M 2 y b q) :
    rayIndex (t,0) p = rayIndex ((M:ℤ)+1,0) p := by
  apply slitBarrier_row_index_eq_right_boundary_of_trace_gap M hM b y 0 t
    (by omega) (by omega) (by omega) hbt q p hallowed _ t (by omega) htM
  intro i _ _ he
  have hv := q.fst_mem_support_of_mem_edges he
  have hh := hq _ hv
  norm_num at hh

/-- Every row strictly to the right of the whole source trace carries the
right-boundary index, including the original expanded top and bottom ports. -/
theorem slitBarrier_right_of_trace_index_eq_boundary
    (M : ℕ) (hM : 2 ≤ M) (b y Y t : ℤ)
    (hY0 : 0 ≤ Y) (hYM : Y ≤ (M:ℤ)) (h2t : 2 < t) (hbt : b < t)
    (htM : t ≤ (M:ℤ)+1)
    (q : squareLattice.Walk (b,0) (2,y))
    (hq : ∀ z ∈ q.support, z.1 < t)
    (p : squareLattice.Walk (b,0) (b,0))
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M 2 y b q) :
    rayIndex (t,Y) p = rayIndex ((M:ℤ)+1,Y) p := by
  apply slitBarrier_row_index_eq_right_boundary_of_trace_gap M hM b y Y t
    hY0 hYM h2t hbt q p hallowed _ t (by omega) htM
  intro i hti _ he
  have hv := q.fst_mem_support_of_mem_edges he
  have hh := hq (i,Y-1) hv
  omega

end PottsContinuity.Push
