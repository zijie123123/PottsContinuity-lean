-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitEdgeEquiv.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitBoundaryLift
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The base of a split vertex lies on the wired arc exactly when the split
vertex is one of the two explicit boundary copies. -/
theorem slitBoxSplitBase_mem_arc_iff (n : ℕ) (x : SlitBoxSplitCoverVertex n) :
    slitBoxSplitBaseVertex n x ∈ slitBoxWiredArc n ↔
      x ∈ slitBoxSplitCoverBoundary n := by
  cases x with
  | inl u =>
    constructor
    · intro h
      exact (u.2 h).elim
    · intro h
      rcases h with ⟨w, hw⟩
      cases hw
  | inr v =>
    constructor
    · intro _
      exact ⟨v, rfl⟩
    · intro _
      exact v.1.property

theorem slitBoxSplitBase_not_boundary_implies_interior (n : ℕ)
    (x : SlitBoxSplitCoverVertex n) (h : x ∉ slitBoxSplitCoverBoundary n) :
    ∃ u : SlitBoxInteriorVertex n, x = Sum.inl u := by
  cases x with
  | inl u => exact ⟨u, rfl⟩
  | inr v => exact (h ⟨v, rfl⟩).elim

theorem slitBoxSplitBase_eq_cases (n : ℕ) (x y : SlitBoxSplitCoverVertex n)
    (h : slitBoxSplitBaseVertex n x = slitBoxSplitBaseVertex n y) :
    x = y ∨ x ∈ slitBoxSplitCoverBoundary n ∧ y ∈ slitBoxSplitCoverBoundary n := by
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      left
      apply congrArg Sum.inl
      apply Subtype.ext
      exact h
    | inr v =>
      change u.1 = v.1.1 at h
      have huArc : u.1 ∈ slitBoxWiredArc n := h ▸ v.1.property
      exact (u.2 huArc).elim
  | inr u =>
    cases y with
    | inl v =>
      change u.1.1 = v.1 at h
      have hvArc : v.1 ∈ slitBoxWiredArc n := h ▸ u.1.property
      exact (v.2 hvArc).elim
    | inr v =>
      right
      exact ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩

def slitBoxSplitBaseGraphHom (n : ℕ) :
    slitBoxSplitCoverGraph n →g slitBoxGraph n where
  toFun := slitBoxSplitBaseVertex n
  map_rel' := by
    intro x y hxy
    have hsq : squareLattice.Adj
        (slitBoxSplitBaseVertex n x).val (slitBoxSplitBaseVertex n y).val := by
      have h := hxy.1.1
      simpa only [slitBoxSplitCoverMap_projection_base] using h
    apply (slitBoxGraph_adj_iff n _ _).mpr
    refine ⟨hsq, ?_⟩
    intro harc
    have hx : x ∈ slitBoxSplitCoverBoundary n :=
      (slitBoxSplitBase_mem_arc_iff n x).mp
        ((mem_slitBoxWiredArc_iff n _).mpr harc.1)
    have hy : y ∈ slitBoxSplitCoverBoundary n :=
      (slitBoxSplitBase_mem_arc_iff n y).mp
        ((mem_slitBoxWiredArc_iff n _).mpr harc.2)
    exact hxy.2 ⟨hx, hy⟩

def slitBoxSplitEdgeMap (n : ℕ) :
    (slitBoxSplitCoverGraph n).edgeSet → (slitBoxGraph n).edgeSet :=
  fun e => ⟨Sym2.map (slitBoxSplitBaseVertex n) e.val,
    (slitBoxSplitBaseGraphHom n).map_mem_edgeSet e.property⟩

private theorem slitBoxSplitGraph_edge_endpoints_eq (n : ℕ)
    {a b c d : SlitBoxSplitCoverVertex n}
    (hab : (slitBoxSplitCoverGraph n).Adj a b)
    (hcd : (slitBoxSplitCoverGraph n).Adj c d)
    (hac : slitBoxSplitBaseVertex n a = slitBoxSplitBaseVertex n c)
    (hbd : slitBoxSplitBaseVertex n b = slitBoxSplitBaseVertex n d) :
    a = c ∧ b = d := by
  rcases slitBoxSplitBase_eq_cases n a c hac with hac | ⟨haB, hcB⟩
  · subst c
    rcases slitBoxSplitBase_eq_cases n b d hbd with hbd | ⟨hbB, hdB⟩
    · exact ⟨rfl, hbd⟩
    · by_cases ha : a ∈ slitBoxSplitCoverBoundary n
      · exact False.elim (hab.2 ⟨ha, hbB⟩)
      · obtain ⟨u, rfl⟩ := slitBoxSplitBase_not_boundary_implies_interior n a ha
        have huniq := slitBoxSplitCoverGraph_boundary_neighbor_unique n u b d hbB hdB
          (by simpa using hab) (by simpa [hbd] using hcd)
        exact ⟨rfl, huniq⟩
  · rcases slitBoxSplitBase_eq_cases n b d hbd with hbd | ⟨hbB, hdB⟩
    · subst d
      have hbOut : b ∉ slitBoxSplitCoverBoundary n := by
        intro hb
        exact hab.2 ⟨haB, hb⟩
      obtain ⟨u, rfl⟩ := slitBoxSplitBase_not_boundary_implies_interior n b hbOut
      have huniq := slitBoxSplitCoverGraph_boundary_neighbor_unique n u a c haB hcB
        (by simpa using hab.symm) (by simpa using hcd.symm)
      exact ⟨huniq, rfl⟩
    · exact False.elim (hab.2 ⟨haB, hbB⟩)

 theorem slitBoxSplitEdgeMap_injective (n : ℕ) :
    Function.Injective (slitBoxSplitEdgeMap n) := by
  intro e₁ e₂ he
  apply Subtype.ext
  obtain ⟨⟨a, b⟩, habPair⟩ := Sym2.mk_surjective e₁.val
  obtain ⟨⟨c, d⟩, hcdPair⟩ := Sym2.mk_surjective e₂.val
  have hab : (slitBoxSplitCoverGraph n).Adj a b := by
    have hp := e₁.property
    rw [← habPair] at hp
    exact (slitBoxSplitCoverGraph n).mem_edgeSet.mp hp
  have hcd : (slitBoxSplitCoverGraph n).Adj c d := by
    have hp := e₂.property
    rw [← hcdPair] at hp
    exact (slitBoxSplitCoverGraph n).mem_edgeSet.mp hp
  have hmap : Sym2.map (slitBoxSplitBaseVertex n) s(a,b) =
      Sym2.map (slitBoxSplitBaseVertex n) s(c,d) := by
    have h := congrArg Subtype.val he
    change Sym2.map (slitBoxSplitBaseVertex n) e₁.val =
      Sym2.map (slitBoxSplitBaseVertex n) e₂.val at h
    rw [← habPair, ← hcdPair] at h
    exact h
  rw [Sym2.map_mk, Sym2.map_mk] at hmap
  rcases Sym2.eq_iff.mp hmap with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · rcases slitBoxSplitGraph_edge_endpoints_eq n hab hcd hac hbd with ⟨rfl, rfl⟩
    rw [← habPair, ← hcdPair]
  · have hends := slitBoxSplitGraph_edge_endpoints_eq n hab hcd.symm had hbc
    rcases hends with ⟨rfl, rfl⟩
    rw [← habPair, ← hcdPair]
    apply Sym2.eq_iff.mpr
    exact Or.inr ⟨rfl, rfl⟩

 theorem slitBoxSplitEdgeMap_surjective (n : ℕ) :
    Function.Surjective (slitBoxSplitEdgeMap n) := by
  intro e
  obtain ⟨⟨u, v⟩, huvPair⟩ := Sym2.mk_surjective e.val
  have huv : (slitBoxGraph n).Adj u v := by
    have hp := e.property
    rw [← huvPair] at hp
    exact (slitBoxGraph n).mem_edgeSet.mp hp
  obtain ⟨x, y, hxy, hx, hy⟩ := slitBoxSplitCoverGraph_lifts_slit_edge n u v huv
  refine ⟨⟨s(x,y), (slitBoxSplitCoverGraph n).mem_edgeSet.mpr hxy⟩, ?_⟩
  apply Subtype.ext
  change Sym2.map (slitBoxSplitBaseVertex n) s(x,y) = e.val
  rw [Sym2.map_mk, hx, hy]
  exact huvPair

noncomputable def slitBoxSplitEdgeEquiv (n : ℕ) :
    (slitBoxSplitCoverGraph n).edgeSet ≃ (slitBoxGraph n).edgeSet :=
  Equiv.ofBijective (slitBoxSplitEdgeMap n)
    ⟨slitBoxSplitEdgeMap_injective n, slitBoxSplitEdgeMap_surjective n⟩

theorem slitBoxSplitEdgeEquiv_val (n : ℕ)
    (e : (slitBoxSplitCoverGraph n).edgeSet) :
    (slitBoxSplitEdgeEquiv n e).val =
      Sym2.map (slitBoxSplitBaseVertex n) e.val := rfl

end PottsContinuity.FKC.FiniteFK
