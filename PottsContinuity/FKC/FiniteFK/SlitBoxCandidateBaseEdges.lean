-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateBaseEdges.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxFinitePolygonCandidates
public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnEdges
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

private theorem slitBoxCandidateReturn_horizontal_bound
    (n : ℕ) (u : SlitBoxVertex n) (huX : 0 ≤ u.val.1) :
    u.val.1.toNat ≤ n := by
  have hbox := u.property
  rw [mem_latticeRectangle] at hbox
  have hx := hbox.1.2
  have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
    push_cast
    omega
  rw [hmax] at hx
  have hcast : (u.val.1.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg huX]
    exact hx
  exact_mod_cast hcast

private theorem slitBoxCandidateReturn_vertical_bound
    (n : ℕ) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    t.val.2.toNat ≤ n := by
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  have hcast : (t.val.2.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg htArc.2.1]
    exact htArc.2.2
  exact_mod_cast hcast

def slitBoxBaseToAllOpenHomForEdges (n : ℕ)
    (A : Configuration (slitBoxGraph n)) [Fintype (slitBoxGraph n).edgeSet
    ] (hA : A = Finset.univ) :
    slitBoxGraph n →g openGraph (slitBoxGraph n) A where
  toFun := id
  map_rel' := by
    intro x y hxy
    apply (openGraph_adj (slitBoxGraph n) A x y).2
    change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
    rw [hA]
    refine ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩, ?_, rfl⟩
    exact Finset.mem_univ _

private theorem slitBoxCanonicalReturn_last_vertical_edge_mem
    (n : ℕ) (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ))
    (huX : 0 ≤ u.val.1) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    s((u.val.1, -(n + 1 : ℤ)), u.val) ∈
      (slitBoxCanonicalReturnWalk n u huY huX t ht).edges := by
  have ha := slitBoxCandidateReturn_horizontal_bound n u huX
  have hk := slitBoxCandidateReturn_vertical_bound n t ht
  have hedgeNat : s(((u.val.1.toNat : ℤ), -(n + 1 : ℤ)),
      ((u.val.1.toNat : ℤ), -(n : ℤ))) ∈
      (slitBoxExteriorReturnWalkNat n u.val.1.toNat t.val.2.toNat ha hk).val.edges := by
    have hp5 := slitReturnVerticalUpWalk_edge_mem (u.val.1.toNat : ℤ)
      (-(n + 1 : ℤ)) 1 (-(n + 1 : ℤ)) (by omega) (by omega)
    simp only [slitBoxExteriorReturnWalkNat, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_append, List.mem_append] at *
    aesop
  have hstart : (u.val.1.toNat : ℤ) = u.val.1 := Int.toNat_of_nonneg huX
  have hend : ((u.val.1.toNat : ℤ), -(n : ℤ)) = u.val := by
    apply Prod.ext
    · exact hstart
    · exact huY.symm
  have hedgeNat' : s((u.val.1, -(n + 1 : ℤ)), u.val) ∈
      (slitBoxExteriorReturnWalkNat n u.val.1.toNat t.val.2.toNat ha hk).val.edges := by
    have hpair : s(((u.val.1.toNat : ℤ), -(n + 1 : ℤ)),
        ((u.val.1.toNat : ℤ), -(n : ℤ))) = s((u.val.1, -(n + 1 : ℤ)), u.val) := by
      apply Sym2.eq_iff.mpr
      exact Or.inl ⟨Prod.ext hstart rfl, hend⟩
    exact hpair ▸ hedgeNat
  simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.edges_copy, ha, hk] using hedgeNat'

private theorem slitBoxCanonicalReturn_has_no_slit_edge
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    {a b : SlitBoxVertex n} (hab : (slitBoxGraph n).Adj a b) :
    s(a.val, b.val) ∉ (slitBoxCanonicalReturnWalk n u huY huX t ht).edges := by
  intro hreturn
  let r := slitBoxCanonicalReturnWalk n u huY huX t ht
  have hr : r.IsPath := slitBoxCanonicalReturnWalk_isPath n hn u huY huX t ht
  have haSupport : a.val ∈ r.support :=
    SimpleGraph.Walk.fst_mem_support_of_mem_edges r hreturn
  have hbSupport : b.val ∈ r.support :=
    SimpleGraph.Walk.snd_mem_support_of_mem_edges r hreturn
  have haBox := a.property
  have hbBox := b.property
  have haClass : a.val = u.val ∨
      (a.val.1 = 0 ∧ 0 ≤ a.val.2 ∧ a.val.2 ≤ (n : ℤ)) :=
    slitBoxCanonicalReturnWalk_support_in_box n u huY huX t ht haSupport haBox
  have hbClass : b.val = u.val ∨
      (b.val.1 = 0 ∧ 0 ≤ b.val.2 ∧ b.val.2 ≤ (n : ℤ)) :=
    slitBoxCanonicalReturnWalk_support_in_box n u huY huX t ht hbSupport hbBox
  have hsq := (slitBoxGraph_adj_iff n a b).mp hab |>.1
  have hnotBothArc := (slitBoxGraph_adj_iff n a b).mp hab |>.2
  rcases haClass with haBottom | haArc
  · rcases hbClass with hbBottom | hbArc
    · have habEq : a.val = b.val := haBottom.trans hbBottom.symm
      rw [habEq] at hsq
      exact squareLattice.loopless.irrefl _ hsq
    · have hpenArc : b.val = r.penultimate := by
        have h' : s(u.val, b.val) ∈ r.edges := by
          simpa [r, haBottom, huY] using hreturn
        exact hr.eq_penultimate_of_mem_edges h'
      have hpenLast : (u.val.1, -(n + 1 : ℤ)) = r.penultimate := by
        have h' : s(u.val, (u.val.1, -(n + 1 : ℤ))) ∈ r.edges := by
          have h0 := slitBoxCanonicalReturn_last_vertical_edge_mem n u huY huX t ht
          have hswap : s((u.val.1, -(n + 1 : ℤ)), u.val) =
              s(u.val, (u.val.1, -(n + 1 : ℤ))) := Sym2.eq_swap ..
          exact hswap ▸ h0
        exact hr.eq_penultimate_of_mem_edges h'
      have hEq : b.val = (u.val.1, -(n + 1 : ℤ)) := hpenArc.trans hpenLast.symm
      have hbY := hbArc.2.1
      rw [hEq] at hbY
      simp only at hbY
      omega
  · rcases hbClass with hbBottom | hbArc
    · have hpenArc : a.val = r.penultimate := by
        have h' : s(u.val, a.val) ∈ r.edges := by
          have hswap : s(a.val, b.val) = s(u.val, a.val) := by
            rw [hbBottom]
            exact Sym2.eq_swap ..
          exact hswap ▸ hreturn
        exact hr.eq_penultimate_of_mem_edges h'
      have hpenLast : (u.val.1, -(n + 1 : ℤ)) = r.penultimate := by
        have h' : s(u.val, (u.val.1, -(n + 1 : ℤ))) ∈ r.edges := by
          have h0 := slitBoxCanonicalReturn_last_vertical_edge_mem n u huY huX t ht
          have hswap : s((u.val.1, -(n + 1 : ℤ)), u.val) =
              s(u.val, (u.val.1, -(n + 1 : ℤ))) := Sym2.eq_swap ..
          exact hswap ▸ h0
        exact hr.eq_penultimate_of_mem_edges h'
      have hEq : a.val = (u.val.1, -(n + 1 : ℤ)) := hpenArc.trans hpenLast.symm
      have haY := haArc.2.1
      rw [hEq] at haY
      simp only at haY
      omega
    · exact hnotBothArc ⟨haArc, hbArc⟩

/-- For a genuine slit edge, membership in the candidate's closed cycle is
exactly membership in its retained original ordered path. The canonical return
contributes no slit-graph edge, including in the scale-one bottom-to-arc case. -/
theorem slitBoxFirstHitCandidateCycle_slitEdge_mem_iff
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) (e : (slitBoxGraph n).edgeSet) :
    Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val ∈
        (slitBoxFirstHitCandidateCycle n hn u huY huX p).edges ↔
      e.val ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  let hA : A = Finset.univ := rfl
  let t := p.val.1
  let r := slitBoxCanonicalReturnWalk n u huY huX t p.property.1
  let f := slitBoxBaseToAllOpenHomForEdges n A hA
  let preWalk : squareLattice.Walk u.val t.val :=
    ((p.val.2 : (slitBoxGraph n).Walk u t).map f).map
      (slitBoxOpenGraphToSquareLatticeHom n A)
  have hcycle : slitBoxFirstHitCandidateCycle n hn u huY huX p = preWalk.append r := by
    rfl
  have hNoReturn : Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val ∉
      r.edges := by
    obtain ⟨⟨a, b⟩, habPair⟩ := Sym2.mk_surjective e.val
    have hadj : (slitBoxGraph n).Adj a b := by
      have h := e.property
      rw [← habPair] at h
      exact (slitBoxGraph n).mem_edgeSet.mp h
    have hNo := slitBoxCanonicalReturn_has_no_slit_edge n hn u huY huX t
      p.property.1 hadj
    have hNo' : s(a.val, b.val) ∉ r.edges := by
      simpa [r] using hNo
    have hmap : Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) e.val =
        s(a.val, b.val) := by
      rw [← habPair]
      change Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex) s(a, b) = _
      simp
    exact hmap ▸ hNo'
  rw [hcycle, SimpleGraph.Walk.edges_append]
  have hprefixEdges : preWalk.edges =
      List.map (Sym2.map (Subtype.val : SlitBoxVertex n → LatticeVertex))
        (p.val.2 : (slitBoxGraph n).Walk u t).edges := by
    change ((((p.val.2 : (slitBoxGraph n).Walk u t).map f).map
      (slitBoxOpenGraphToSquareLatticeHom n A)).edges) = _
    rw [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map]
    simp [f, slitBoxBaseToAllOpenHomForEdges,
      slitBoxOpenGraphToSquareLatticeHom]
  constructor
  · intro h
    rw [hprefixEdges, List.mem_append] at h
    rcases h with hprefix | hreturn
    · rw [List.mem_map] at hprefix
      obtain ⟨e', he', heq⟩ := hprefix
      have : e' = e.val := Sym2.map.injective Subtype.val_injective heq
      simpa [this] using he'
    · exact (hNoReturn (by simpa [r] using hreturn)).elim
  · intro he
    rw [hprefixEdges, List.mem_append]
    left
    exact List.mem_map.mpr ⟨e.val, he, rfl⟩

end PottsContinuity.FKC.FiniteFK
