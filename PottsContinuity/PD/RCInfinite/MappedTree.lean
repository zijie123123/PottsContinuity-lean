-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/MappedTree.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
noncomputable section
open scoped Classical

def mappedTreeDeleteIso {V W : Type*} (H : SimpleGraph V) (f : V ↪ W) (v : V) :
    H.deleteIncidenceSet v ≃g
      ((H.map f).deleteIncidenceSet (f v)).induce (Set.range f) where
  toEquiv :=
    { toFun := fun x => ⟨f x, Set.mem_range.mpr ⟨x, rfl⟩⟩
      invFun := fun y => Classical.choose y.property
      left_inv := by
        intro x
        apply f.injective
        exact Classical.choose_spec (Set.mem_range.mpr ⟨x, rfl⟩)
      right_inv := by
        intro y
        apply Subtype.ext
        exact Classical.choose_spec y.property }
  map_rel_iff' := by
    intro x y
    simp only [SimpleGraph.induce_adj]
    change ((H.map f).deleteIncidenceSet (f v)).Adj (f x) (f y) ↔
      (H.deleteIncidenceSet v).Adj x y
    rw [SimpleGraph.deleteIncidenceSet_adj, SimpleGraph.deleteIncidenceSet_adj,
      SimpleGraph.map_adj_apply]
    constructor
    · rintro ⟨hxy, hxv, hyv⟩
      exact ⟨hxy, fun h => hxv (congrArg f h), fun h => hyv (congrArg f h)⟩
    · rintro ⟨hxy, hxv, hyv⟩
      exact ⟨hxy, fun h => hxv (f.injective h), fun h => hyv (f.injective h)⟩

theorem mapped_tree_delete_reachable_iff {V W : Type*} (H : SimpleGraph V)
    (f : V ↪ W) (v a b : V) :
    ((H.map f).deleteIncidenceSet (f v)).Reachable (f a) (f b) ↔
      (H.deleteIncidenceSet v).Reachable a b := by
  constructor
  · intro h
    let G := (H.map f).deleteIncidenceSet (f v)
    let S : Set W := Set.range f
    let q : W → S := fun x =>
      if hx : x ∈ S then ⟨x, hx⟩ else ⟨f a, Set.mem_range.mpr ⟨a, rfl⟩⟩
    let hq : G →g G.induce S :=
      { toFun := q
        map_rel' := by
          intro x y hxy
          have hbase : (H.map f).Adj x y := SimpleGraph.deleteIncidenceSet_le _ _ hxy
          obtain ⟨u, w, _, hxu, hyw⟩ := (SimpleGraph.map_adj f H x y).mp hbase
          have hx : x ∈ S := ⟨u, hxu⟩
          have hy : y ∈ S := ⟨w, hyw⟩
          simpa [q, hx, hy] using hxy }
    have hq_apply (x : W) : hq x = q x := by
      change hq.toFun x = q x
      rfl
    obtain ⟨w⟩ := h
    have hfa : f a ∈ S := ⟨a, rfl⟩
    have hfb : f b ∈ S := ⟨b, rfl⟩
    have hqa : q (f a) = ⟨f a, hfa⟩ := by simp [q, hfa]
    have hqb : q (f b) = ⟨f b, hfb⟩ := by simp [q, hfb]
    have hInd : (G.induce S).Reachable
        ⟨f a, Set.mem_range.mpr ⟨a, rfl⟩⟩ ⟨f b, Set.mem_range.mpr ⟨b, rfl⟩⟩ := by
      have hw := w.map hq
      rw [hq_apply, hq_apply] at hw
      rw [← hqa, ← hqb]
      exact hw.reachable
    exact (mappedTreeDeleteIso H f v).reachable_iff.mp hInd
  · intro h
    have hInd := (mappedTreeDeleteIso H f v).reachable_iff.mpr h
    let inc : ((H.map f).deleteIncidenceSet (f v)).induce (Set.range f) →g
        (H.map f).deleteIncidenceSet (f v) :=
      { toFun := Subtype.val, map_rel' := fun h => h }
    exact hInd.map inc

end
end PottsContinuity.PD.RCInfinite
