-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/SimplePathTwoEdgeCut.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FirstHitPathDecomposition
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

private theorem walk_exists_edge_crossing_set
    {V : Type*} {G : SimpleGraph V} {A : Set V} {x y : V}
    (w : G.Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ e, e ∈ w.edges ∧ ∀ a b, e = s(a,b) → (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A) := by
  induction w with
  | nil => exact (hy hx).elim
  | @cons x z y hxz tail ih =>
      by_cases hz : z ∈ A
      · obtain ⟨e, he, hcross⟩ := ih hz hy
        exact ⟨e, by simp [he], hcross⟩
      · refine ⟨s(x,z), by simp, ?_⟩
        intro a b hab
        rcases Sym2.eq_iff.mp hab with ⟨hxa, hzb⟩ | ⟨hxb, hza⟩
        · subst a; subst b
          exact Or.inl ⟨hx, hz⟩
        · subst a; subst b
          exact Or.inr ⟨hz, hx⟩

private theorem path_inside_inside_with_outside_two_crossings
    {V : Type*} {G : SimpleGraph V} {A : Set V} {x y : V}
    (w : G.Walk x y) (hw : w.IsPath) (hx : x ∈ A) (hy : y ∈ A)
    (hout : ∃ z, z ∈ w.support ∧ z ∉ A) :
    ∃ e₁ e₂, e₁ ∈ w.edges ∧ e₂ ∈ w.edges ∧ e₁ ≠ e₂ ∧
      (∀ a b, e₁ = s(a,b) → (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) ∧
      (∀ a b, e₂ = s(a,b) → (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) := by
  induction w with
  | nil =>
      rcases hout with ⟨z, hz, hza⟩
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact (hza (hz ▸ hx)).elim
  | @cons x z y hxz tail ih =>
      have hpath := (SimpleGraph.Walk.cons_isPath_iff hxz tail).mp hw
      have houtTail : ∃ a, a ∈ tail.support ∧ a ∉ A := by
        rcases hout with ⟨a, ha, hna⟩
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact (hna hx).elim
        · exact ⟨a, ha, hna⟩
      by_cases hz : z ∈ A
      · obtain ⟨e₁, e₂, he₁, he₂, hne, hc₁, hc₂⟩ := ih hpath.1 hz hy houtTail
        refine ⟨e₁, e₂, ?_, ?_, hne, hc₁, hc₂⟩ <;> simp [he₁, he₂]
      · obtain ⟨e₂, he₂, hc₂⟩ := walk_exists_edge_crossing_set tail.reverse hy hz
        have he₂' : e₂ ∈ tail.edges := by simpa [SimpleGraph.Walk.edges_reverse] using he₂
        refine ⟨s(x,z), e₂, by simp, ?_, ?_, ?_, hc₂⟩
        · simp [he₂']
        · intro heq
          have hxa : x ∈ tail.support := by
            have hedge : s(x,z) ∈ tail.edges := by simpa [heq] using he₂'
            exact tail.fst_mem_support_of_mem_edges hedge
          exact hpath.2 hxa
        · intro a b hab
          rcases Sym2.eq_iff.mp hab with ⟨hxa, hzb⟩ | ⟨hxb, hza⟩
          · subst a; subst b
            exact Or.inl ⟨hx, hz⟩
          · subst a; subst b
            exact Or.inr ⟨hz, hx⟩

/-- A simple path crossing a cut of at most two edges cannot leave the set
after its first hit. The returned split is the exact first-hit append split. -/
theorem walk_exists_first_hit_decomposition_of_two_edge_cut
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {A : Set V} {x y : V}
    (F : Finset (Sym2 V)) (hF : F.card ≤ 2)
    (w : G.Walk x y)
    (hcut : ∀ a b, s(a,b) ∈ w.edges →
      ((a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) → s(a,b) ∈ F)
    (hx : x ∉ A) (hy : y ∈ A) (hw : w.IsPath) :
    ∃ b, b ∈ A ∧ ∃ q : G.Walk x b, ∃ r : G.Walk b y,
      q.IsPath ∧ r.IsPath ∧ q.append r = w ∧
      (∀ z, z ∈ q.support → z ∈ A → z = b) ∧
      (∀ z, z ∈ r.support → z ∈ A) ∧
      (∀ e, e ∈ q.edges → e ∈ w.edges) ∧
      (∀ e, e ∈ r.edges → e ∈ w.edges) := by
  classical
  obtain ⟨b, hb, q, r, hq, hsplit, hfirst, hqSupport, hqEdges⟩ :=
    PottsContinuity.FKC.FiniteFK.walk_exists_first_hit_decomposition w hy hw
  have hrpath : r.IsPath := by
    have happend : (q.append r).IsPath := hsplit ▸ hw
    exact happend.of_append_right
  have hrEdges : ∀ e, e ∈ r.edges → e ∈ w.edges := by
    intro e he
    have hedgeEq : q.edges ++ r.edges = w.edges := by
      have := congrArg SimpleGraph.Walk.edges hsplit
      simpa [SimpleGraph.Walk.edges_append] using this
    rw [← hedgeEq]
    exact List.mem_append.mpr (Or.inr he)
  have hqCross : ∃ e, e ∈ q.edges ∧
      (∀ a b, e = s(a,b) → (a ∈ A ∧ b ∉ A) ∨ (a ∉ A ∧ b ∈ A)) := by
    obtain ⟨e, he, hc⟩ := walk_exists_edge_crossing_set q.reverse hb hx
    exact ⟨e, by simpa [SimpleGraph.Walk.edges_reverse] using he, hc⟩
  have hrNoOutside : ∀ z, z ∈ r.support → z ∈ A := by
    intro z hz
    by_contra hza
    obtain ⟨e₀, he₀, hc₀⟩ := hqCross
    obtain ⟨e₁, e₂, he₁, he₂, hne, hc₁, hc₂⟩ :=
      path_inside_inside_with_outside_two_crossings r hrpath hb hy ⟨z, hz, hza⟩
    have hnot01 : e₀ ≠ e₁ := by
      intro heq
      have hnodup : (q.edges ++ r.edges).Nodup := by
        have := hw.isTrail.edges_nodup
        simpa [← SimpleGraph.Walk.edges_append, hsplit] using this
      have hdisj := (List.nodup_append.mp hnodup).2.2
      exact hdisj e₀ he₀ e₁ he₁ heq
    have hnot02 : e₀ ≠ e₂ := by
      intro heq
      have hnodup : (q.edges ++ r.edges).Nodup := by
        have := hw.isTrail.edges_nodup
        simpa [← SimpleGraph.Walk.edges_append, hsplit] using this
      have hdisj := (List.nodup_append.mp hnodup).2.2
      exact hdisj e₀ he₀ e₂ he₂ heq
    have he₀F : e₀ ∈ F := by
      rcases Sym2.mk_surjective e₀ with ⟨⟨a,b⟩, rfl⟩
      rcases hc₀ a b rfl with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · exact hcut a b (hqEdges (s(a,b)) he₀) (Or.inl ⟨ha,hb'⟩)
      · exact hcut a b (hqEdges (s(a,b)) he₀) (Or.inr ⟨ha,hb'⟩)
    have he₁F : e₁ ∈ F := by
      rcases Sym2.mk_surjective e₁ with ⟨⟨a,b⟩, rfl⟩
      rcases hc₁ a b rfl with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · exact hcut a b (hrEdges (s(a,b)) he₁) (Or.inl ⟨ha,hb'⟩)
      · exact hcut a b (hrEdges (s(a,b)) he₁) (Or.inr ⟨ha,hb'⟩)
    have he₂F : e₂ ∈ F := by
      rcases Sym2.mk_surjective e₂ with ⟨⟨a,b⟩, rfl⟩
      rcases hc₂ a b rfl with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · exact hcut a b (hrEdges (s(a,b)) he₂) (Or.inl ⟨ha,hb'⟩)
      · exact hcut a b (hrEdges (s(a,b)) he₂) (Or.inr ⟨ha,hb'⟩)
    have hthree : ({e₀, e₁, e₂} : Finset (Sym2 V)) ⊆ F := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact he₀F
      · exact he₁F
      · exact he₂F
    have hcard := Finset.card_le_card hthree
    have hthreeCard : ({e₀, e₁, e₂} : Finset (Sym2 V)).card = 3 := by
      simp [hnot01, hnot02, hne]
    rw [hthreeCard] at hcard
    omega
  exact ⟨b, hb, q, r, hq, hrpath, hsplit, hfirst, hrNoOutside,
    hqEdges, hrEdges⟩

end PottsContinuity.FKC.Medial
