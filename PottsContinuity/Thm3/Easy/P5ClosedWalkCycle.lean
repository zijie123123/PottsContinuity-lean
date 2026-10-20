module

public import PottsContinuity.PD.Duality.RayIndexSeparation
public import PottsContinuity.PlanarTopology.InterlacedPaths
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

private theorem duplicate_dropUntil_facts
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (hdup : List.Duplicate x p.support) :
    ∃ hx : x ∈ p.support,
      x ∈ (p.dropUntil x hx).tail.support ∧ ¬ (p.dropUntil x hx).Nil := by
  induction p with
  | nil => simp at hdup
  | @cons a b c hadj tail ih =>
      change List.Duplicate x (a :: tail.support) at hdup
      rw [List.duplicate_cons_iff] at hdup
      rcases hdup with ⟨ha, hx⟩ | hdupTail
      · subst a
        refine ⟨List.mem_cons_self, ?_⟩
        simp [SimpleGraph.Walk.dropUntil, hx]
      · by_cases hax : a = x
        · subst a
          refine ⟨List.mem_cons_self, ?_⟩
          simp [SimpleGraph.Walk.dropUntil, hdupTail.mem]
        · obtain ⟨hxTail, hfacts⟩ := ih hdupTail
          let hxCons : x ∈ (SimpleGraph.Walk.cons hadj tail).support :=
            List.mem_cons_of_mem a hxTail
          refine ⟨hxCons, ?_⟩
          cases tail with
          | nil => simp at hdupTail
          | cons hbc tail' =>
              have hdrop : (SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.cons hbc tail')).dropUntil x hxCons =
                  (SimpleGraph.Walk.cons hbc tail').dropUntil x hxTail := by
                simp only [SimpleGraph.Walk.dropUntil]
                split_ifs with hB
                · rfl
                · rfl
              rw [hdrop]
              exact hfacts

private theorem rayStep_reverse_zero (x u v : PD.FK.LatticeVertex)
    (h : PD.FK.squareLattice.Adj u v) :
    rayStep x u v + rayStep x v u = 0 := by
  have hcoord := (PD.FK.squareLattice_adj_iff u v).mp h
  rcases hcoord with hhor | hver
  · simp [rayStep, hhor.2]
  · simp [rayStep, hver.1]; omega

private theorem rayIndex_nonzero_length_ge_three
    {x z : PD.FK.LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z) (hp : rayIndex x p ≠ 0) :
    3 ≤ p.length := by
  by_contra hn
  have hle : p.length ≤ 2 := by omega
  cases p with
  | nil => simp [rayIndex] at hp
  | @cons a b c h₁ tail =>
      cases tail with
      | nil => exact (PD.FK.squareLattice.irrefl h₁).elim
      | @cons b' c' d h₂ tail₂ =>
          cases tail₂ with
          | nil =>
              have hidxzero :
                  rayIndex x (SimpleGraph.Walk.cons h₁
                    (SimpleGraph.Walk.cons h₂ .nil)) = 0 := by
                simp only [rayIndex, Int.add_zero]
                exact rayStep_reverse_zero x z b h₁
              exact hp hidxzero
          | @cons c'' e f h₃ tail₃ =>
              simp only [SimpleGraph.Walk.length_cons] at hle
              omega

/-- A closed lattice walk with nonzero signed ray intersection contains a
simple closed subwalk with nonzero signed ray intersection. The selected
subwalk uses only edges of the original walk. -/
theorem closedWalk_exists_simpleNonzeroRayIndex
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (φ : G →g PD.FK.squareLattice) (x : PD.FK.LatticeVertex) {z : V}
    (p : G.Walk z z) (hp : rayIndex x (p.map φ) ≠ 0) :
    ∃ y : V, ∃ q : G.Walk y y,
      q.IsCycle ∧ rayIndex x (q.map φ) ≠ 0 ∧ q.edges ⊆ p.edges := by
  classical
  let Good : (Σ y : V, G.Walk y y) → Prop := fun w =>
    rayIndex x (w.2.map φ) ≠ 0 ∧ w.2.edges ⊆ p.edges
  obtain ⟨⟨y, q⟩, hqGood, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT Good (fun w => w.2.length)
      ⟨⟨z, p⟩, hp, fun e he => he⟩
  have hqidx : rayIndex x (q.map φ) ≠ 0 := hqGood.1
  have hqedge : q.edges ⊆ p.edges := hqGood.2
  have hqminimal {y' : V} (r : G.Walk y' y')
      (hr : rayIndex x (r.map φ) ≠ 0) (he : r.edges ⊆ p.edges) :
      q.length ≤ r.length := by
    by_contra hn
    have hlt : r.length < q.length := lt_of_not_ge hn
    have hlenle : (fun w : Σ y : V, G.Walk y y => w.2.length) ⟨y', r⟩ ≤
        (fun w : Σ y : V, G.Walk y y => w.2.length) ⟨y, q⟩ := by
      simpa using Nat.le_of_lt hlt
    have hminle := hmin (show Good ⟨y', r⟩ from ⟨hr, he⟩) hlenle
    exact (not_lt_of_ge hminle) hlt
  have hqLength : 3 ≤ q.length := by
    have h := rayIndex_nonzero_length_ge_three (q.map φ) hqidx
    simpa using h
  have hqNonNil : ¬ q.Nil := by
    intro hn
    have he : q = .nil := SimpleGraph.Walk.eq_nil_iff_nil.mpr hn
    subst q
    simp [rayIndex] at hqidx
  have htailPath : q.tail.IsPath := by
    by_contra hnot
    have hnotNodup : ¬ q.tail.support.Nodup := by
      intro hn
      exact hnot ((SimpleGraph.Walk.isPath_def q.tail).2 hn)
    obtain ⟨v, hdup⟩ := (List.exists_duplicate_iff_not_nodup).2 hnotNodup
    obtain ⟨hv, hfacts⟩ := duplicate_dropUntil_facts q.tail hdup
    rcases hfacts with ⟨hvs, hsNonNil⟩
    let t := q.tail.takeUntil v hv
    let s := q.tail.dropUntil v hv
    let bpath := s.tail.takeUntil v hvs
    let cpath := s.tail.dropUntil v hvs
    let loop : G.Walk v v := SimpleGraph.Walk.cons (s.adj_snd hsNonNil) bpath
    let preWalk : G.Walk y v :=
      SimpleGraph.Walk.cons (q.adj_snd hqNonNil) t
    let restLoop : G.Walk y y := preWalk.append cpath
    have hrest : s.tail = bpath.append cpath := (s.tail.take_spec (u := v) hvs).symm
    have hsdecomp : s = loop.append cpath := by
      rw [← s.cons_tail_eq hsNonNil]
      simp [loop, hrest, SimpleGraph.Walk.cons_append]
    have hqtail : q.tail = t.append s := by
      dsimp [t, s]
      exact (q.tail.take_spec (u := v) hv).symm
    have hqdecomp : q = preWalk.append (loop.append cpath) := by
      calc
        q = SimpleGraph.Walk.cons (q.adj_snd hqNonNil) q.tail :=
          (q.cons_tail_eq hqNonNil).symm
        _ = SimpleGraph.Walk.cons (q.adj_snd hqNonNil) (t.append s) := by rw [hqtail]
        _ = preWalk.append (loop.append cpath) := by
          simp [preWalk, hsdecomp, SimpleGraph.Walk.cons_append]
    have hloopidx : rayIndex x (loop.map φ) ≠ 0 ∨
        rayIndex x (restLoop.map φ) ≠ 0 := by
      have hdecompIdx : rayIndex x (q.map φ) =
          rayIndex x (preWalk.map φ) +
            (rayIndex x (loop.map φ) + rayIndex x (cpath.map φ)) := by
        rw [hqdecomp, SimpleGraph.Walk.map_append, SimpleGraph.Walk.map_append,
          PottsContinuity.PlanarTopology.rayIndex_append,
          PottsContinuity.PlanarTopology.rayIndex_append]
      by_contra hn
      push Not at hn
      have hrestIdx : rayIndex x (restLoop.map φ) =
          rayIndex x (preWalk.map φ) + rayIndex x (cpath.map φ) := by
        change rayIndex x ((preWalk.append cpath).map φ) = _
        rw [SimpleGraph.Walk.map_append,
          PottsContinuity.PlanarTopology.rayIndex_append]
      have heqzero : rayIndex x (q.map φ) = 0 := by
        rw [hdecompIdx, hn.1]
        simp only [Int.zero_add]
        rw [← hrestIdx, hn.2]
      exact hqidx heqzero
    rcases hloopidx with hLoop | hRem
    · have hloopEdges : loop.edges ⊆ q.edges := by
        intro e he
        rw [hqdecomp, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append]
        simp only [List.mem_append]
        exact Or.inr (Or.inl he)
      have hloopBound : loop.edges ⊆ p.edges := fun e he => hqedge (hloopEdges he)
      have hlenlt : loop.length < q.length := by
        have hqLen : q.length = preWalk.length + loop.length + cpath.length := by
          rw [hqdecomp, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append]
          simp [Nat.add_assoc]
        have hprePos : 0 < preWalk.length := by
          simp [preWalk, SimpleGraph.Walk.length_cons]
        omega
      exact (not_lt_of_ge (hqminimal loop hLoop hloopBound)) hlenlt
    · have hremEdges : restLoop.edges ⊆ q.edges := by
        intro e he
        have he' : e ∈ preWalk.edges ∨ e ∈ cpath.edges := by
          simpa [restLoop, SimpleGraph.Walk.edges_append] using he
        rw [hqdecomp, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append]
        simp only [List.mem_append]
        rcases he' with he | he
        · exact Or.inl he
        · exact Or.inr (Or.inr he)
      have hremBound : restLoop.edges ⊆ p.edges := fun e he => hqedge (hremEdges he)
      have hlenlt : restLoop.length < q.length := by
        have hqLen : q.length = preWalk.length + loop.length + cpath.length := by
          rw [hqdecomp, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append]
          simp [Nat.add_assoc]
        have hrestLen : restLoop.length = preWalk.length + cpath.length := by
          simp [restLoop, SimpleGraph.Walk.length_append]
        have hloopPos : 0 < loop.length := by
          simp [loop, SimpleGraph.Walk.length_cons]
        rw [hqLen, hrestLen]
        omega
      exact (not_lt_of_ge (hqminimal restLoop hRem hremBound)) hlenlt
  exact ⟨y, q, (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).2
    ⟨htailPath, hqLength⟩, hqidx, hqedge⟩

end PottsContinuity.Thm3.Easy
