-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/Trifurcation.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

def deletedOpenGraph (ω : LatticeConfiguration) (v : LatticeVertex) : SimpleGraph LatticeVertex :=
  (rcInfiniteOpenGraph ω).deleteIncidenceSet v

def deletedCluster (ω : LatticeConfiguration) (v x : LatticeVertex) : Set LatticeVertex :=
  {y | (deletedOpenGraph ω v).Reachable x y}

def deletedInfiniteAt (ω : LatticeConfiguration) (v x : LatticeVertex) : Prop :=
  (deletedCluster ω v x).Infinite

def deletedChain : ℕ → LatticeConfiguration → LatticeVertex → LatticeVertex → LatticeVertex → Prop
  | 0, _, _, x, y => x = y
  | n + 1, ω, v, x, y => ∃ z, (deletedOpenGraph ω v).Adj x z ∧ deletedChain n ω v z y

theorem deletedChain_reachable {n : ℕ} {ω : LatticeConfiguration} {v x y : LatticeVertex}
    (h : deletedChain n ω v x y) : (deletedOpenGraph ω v).Reachable x y := by
  induction n generalizing x with
  | zero => exact h ▸ SimpleGraph.Reachable.refl x
  | succ n ih =>
    obtain ⟨z, hxz, hzy⟩ := h
    exact hxz.reachable.trans (ih hzy)

theorem reachable_iff_deletedChain (ω : LatticeConfiguration) (v x y : LatticeVertex) :
    (deletedOpenGraph ω v).Reachable x y ↔ ∃ n, deletedChain n ω v x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨0, rfl⟩
    | cons h w ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, _, h, hn⟩
  · rintro ⟨n, hn⟩
    exact deletedChain_reachable hn

theorem measurableSet_deleted_adj (v x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | (deletedOpenGraph ω v).Adj x y} := by
  by_cases hx : x = v
  · have heq : {ω : LatticeConfiguration | (deletedOpenGraph ω v).Adj x y} = ∅ := by
      ext ω
      simp [deletedOpenGraph, SimpleGraph.deleteIncidenceSet_adj, hx]
    rw [heq]
    exact MeasurableSet.empty
  · by_cases hy : y = v
    · have heq : {ω : LatticeConfiguration | (deletedOpenGraph ω v).Adj x y} = ∅ := by
        ext ω
        simp [deletedOpenGraph, SimpleGraph.deleteIncidenceSet_adj, hy]
      rw [heq]
      exact MeasurableSet.empty
    · have heq : {ω : LatticeConfiguration | (deletedOpenGraph ω v).Adj x y} =
          {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Adj x y} := by
        ext ω
        simp [deletedOpenGraph, SimpleGraph.deleteIncidenceSet_adj, hx, hy]
      rw [heq]
      exact measurableSet_open_adj x y

theorem measurableSet_deletedChain (n : ℕ) (v x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | deletedChain n ω v x y} := by
  induction n generalizing x with
  | zero =>
      by_cases h : x = y <;> simp [deletedChain, h]
  | succ n ih =>
      have h := MeasurableSet.iUnion (fun z : LatticeVertex =>
        (measurableSet_deleted_adj v x z).inter (ih z))
      convert h using 1
      ext ω
      simp [deletedChain]

theorem measurableSet_deleted_reachable (v x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | (deletedOpenGraph ω v).Reachable x y} := by
  have h := MeasurableSet.iUnion (fun n : ℕ => measurableSet_deletedChain n v x y)
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, reachable_iff_deletedChain, mem_iUnion]

theorem deleted_infinite_iff_escape (ω : LatticeConfiguration) (v x : LatticeVertex) :
    deletedInfiniteAt ω v x ↔ ∀ F : Finset LatticeVertex,
      ∃ y, y ∉ F ∧ (deletedOpenGraph ω v).Reachable x y := by
  constructor
  · intro h F
    obtain ⟨y, hy, hyF⟩ := h.exists_notMem_finset F
    exact ⟨y, hyF, hy⟩
  · intro h hfin
    obtain ⟨y, hyF, hy⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.mpr hy)

theorem measurableSet_deletedInfiniteAt (v x : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | deletedInfiniteAt ω v x} := by
  have hinner (F : Finset LatticeVertex) : MeasurableSet
      (⋃ y : {y : LatticeVertex // y ∉ F},
        {ω : LatticeConfiguration | (deletedOpenGraph ω v).Reachable x y.val}) :=
    MeasurableSet.iUnion fun y => measurableSet_deleted_reachable v x y.val
  have h := MeasurableSet.iInter hinner
  convert h using 1
  ext ω
  change deletedInfiniteAt ω v x ↔ _
  rw [deleted_infinite_iff_escape]
  simp only [mem_iInter, mem_iUnion, Set.mem_ofPred_eq, Subtype.exists, exists_prop]

/-- A trifurcation vertex has three distinct infinite branches when its
incident open edges are removed. -/
def isTrifurcationAt (ω : LatticeConfiguration) (v : LatticeVertex) : Prop :=
  ∃ ys : Fin 3 → LatticeVertex,
    (∀ j, (rcInfiniteOpenGraph ω).Adj v (ys j) ∧ deletedInfiniteAt ω v (ys j)) ∧
      ∀ j k, j ≠ k → ¬(deletedOpenGraph ω v).Reachable (ys j) (ys k)


theorem open_adj_translation_iff (a : LatticeVertex) (ω : LatticeConfiguration)
    (x y : LatticeVertex) :
    (rcInfiniteOpenGraph ω).Adj x y ↔
      (rcInfiniteOpenGraph (edgeTranslate a ω)).Adj
        (latticeTranslate a x) (latticeTranslate a y) := by
  rw [rcInfiniteOpenGraph_adj, rcInfiniteOpenGraph_adj]
  by_cases hxy : squareLattice.Adj x y
  · have he : s(x, y) ∈ squareLattice.edgeSet := squareLattice.mem_edgeSet.mpr hxy
    have ht : s(latticeTranslate a x, latticeTranslate a y) ∈ squareLattice.edgeSet :=
      squareLattice.mem_edgeSet.mpr ((squareLattice_adj_translate_iff a x y).mpr hxy)
    have hstate : edgeTranslate a ω ⟨s(latticeTranslate a x, latticeTranslate a y), ht⟩ =
        ω ⟨s(x, y), he⟩ := edgeTranslate_at_translatedEdge a ω ⟨s(x, y), he⟩
    exact ⟨fun ⟨_, hval⟩ => ⟨ht, hstate ▸ hval⟩,
      fun ⟨_, hval⟩ => ⟨he, hstate.symm ▸ hval⟩⟩
  · have htranslated :
        ¬squareLattice.Adj (latticeTranslate a x) (latticeTranslate a y) :=
      fun h => hxy ((squareLattice_adj_translate_iff a x y).mp h)
    constructor
    · rintro ⟨he, _⟩
      exact (hxy (squareLattice.mem_edgeSet.mp he)).elim
    · rintro ⟨he, _⟩
      exact (htranslated (squareLattice.mem_edgeSet.mp he)).elim

def deletedGraphTranslationIso (a : LatticeVertex) (ω : LatticeConfiguration)
    (v : LatticeVertex) :
    deletedOpenGraph ω v ≃g
      deletedOpenGraph (edgeTranslate a ω) (latticeTranslate a v) where
  toEquiv := {
    toFun := latticeTranslate a
    invFun := latticeTranslate (-a)
    left_inv := latticeTranslate_neg_cancel a
    right_inv := by
      intro x
      ext <;> dsimp [latticeTranslate] <;> omega }
  map_rel_iff' := by
    intro x y
    rw [deletedOpenGraph, deletedOpenGraph,
      SimpleGraph.deleteIncidenceSet_adj, SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro ⟨hxy, hxv, hyv⟩
      refine ⟨(open_adj_translation_iff a ω x y).mpr hxy, ?_, ?_⟩
      · intro heq
        apply hxv
        exact congrArg (latticeTranslate a) heq
      · intro heq
        apply hyv
        exact congrArg (latticeTranslate a) heq
    · rintro ⟨hxy, hxv, hyv⟩
      refine ⟨(open_adj_translation_iff a ω x y).mp hxy, ?_, ?_⟩
      · intro heq
        apply hxv
        have h := congrArg (latticeTranslate (-a)) heq
        simpa [latticeTranslate] using h
      · intro heq
        apply hyv
        have h := congrArg (latticeTranslate (-a)) heq
        simpa [latticeTranslate] using h

theorem deletedCluster_translation (a : LatticeVertex) (ω : LatticeConfiguration)
    (v x : LatticeVertex) :
    deletedCluster (edgeTranslate a ω) (latticeTranslate a v) (latticeTranslate a x) =
      latticeTranslate a '' deletedCluster ω v x := by
  ext y
  obtain ⟨z, rfl⟩ := (latticeTranslationIso a).surjective y
  change (deletedOpenGraph (edgeTranslate a ω) (latticeTranslate a v)).Reachable
      (latticeTranslate a x) (latticeTranslate a z) ↔
    ∃ w ∈ deletedCluster ω v x, latticeTranslate a w = latticeTranslate a z
  constructor
  · intro hy
    exact ⟨z, (deletedGraphTranslationIso a ω v).reachable_iff.mp hy, rfl⟩
  · rintro ⟨w, hw, heq⟩
    have hEq : w = z := (latticeTranslationIso a).injective heq
    subst w
    exact (deletedGraphTranslationIso a ω v).reachable_iff.mpr hw

theorem deletedInfiniteAt_translation (a : LatticeVertex) (ω : LatticeConfiguration)
    (v x : LatticeVertex) :
    deletedInfiniteAt (edgeTranslate a ω) (latticeTranslate a v) (latticeTranslate a x) ↔
      deletedInfiniteAt ω v x := by
  change (deletedCluster (edgeTranslate a ω) (latticeTranslate a v)
      (latticeTranslate a x)).Infinite ↔ (deletedCluster ω v x).Infinite
  rw [deletedCluster_translation]
  have hinj : Set.InjOn (latticeTranslate a) (deletedCluster ω v x) := by
    intro u hu z hz heq
    exact (latticeTranslationIso a).injective heq
  exact Set.infinite_image_iff hinj

theorem latticeTranslate_add_neg_cancel (a x : LatticeVertex) :
    latticeTranslate a (latticeTranslate (-a) x) = x := by
  ext <;> dsimp [latticeTranslate] <;> omega

theorem isTrifurcationAt_translation (a : LatticeVertex) (ω : LatticeConfiguration)
    (v : LatticeVertex) :
    isTrifurcationAt (edgeTranslate a ω) (latticeTranslate a v) ↔
      isTrifurcationAt ω v := by
  constructor
  · rintro ⟨ys, hys, hsep⟩
    refine ⟨fun j => latticeTranslate (-a) (ys j), ?_, ?_⟩
    · intro j
      have hcancel := latticeTranslate_add_neg_cancel a (ys j)
      have hadj : (rcInfiniteOpenGraph (edgeTranslate a ω)).Adj
          (latticeTranslate a v)
          (latticeTranslate a (latticeTranslate (-a) (ys j))) := by
        simpa only [hcancel] using (hys j).1
      have hbranch : deletedInfiniteAt (edgeTranslate a ω) (latticeTranslate a v)
          (latticeTranslate a (latticeTranslate (-a) (ys j))) := by
        simpa only [hcancel] using (hys j).2
      exact ⟨(open_adj_translation_iff a ω v _).mpr hadj,
        (deletedInfiniteAt_translation a ω v _).mp hbranch⟩
    · intro j k hjk hreach
      have htranslated := (deletedGraphTranslationIso a ω v).reachable_iff.mpr hreach
      change (deletedOpenGraph (edgeTranslate a ω) (latticeTranslate a v)).Reachable
        (latticeTranslate a (latticeTranslate (-a) (ys j)))
        (latticeTranslate a (latticeTranslate (-a) (ys k))) at htranslated
      have hcancelj := latticeTranslate_add_neg_cancel a (ys j)
      have hcancelk := latticeTranslate_add_neg_cancel a (ys k)
      apply hsep j k hjk
      simpa only [hcancelj, hcancelk] using htranslated
  · rintro ⟨ys, hys, hsep⟩
    refine ⟨fun j => latticeTranslate a (ys j), ?_, ?_⟩
    · intro j
      have hadj := (open_adj_translation_iff a ω v (ys j)).mp (hys j).1
      exact ⟨hadj, (deletedInfiniteAt_translation a ω v (ys j)).mpr (hys j).2⟩
    · intro j k hjk hreach
      apply hsep j k hjk
      exact (deletedGraphTranslationIso a ω v).reachable_iff.mp hreach


theorem measurableSet_isTrifurcationAt (v : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | isTrifurcationAt ω v} := by
  have hsep (ys : Fin 3 → LatticeVertex) (j k : Fin 3) : MeasurableSet
      {ω : LatticeConfiguration | j = k ∨
        ¬(deletedOpenGraph ω v).Reachable (ys j) (ys k)} := by
    by_cases hjk : j = k
    · simp [hjk]
    · have heq : {ω : LatticeConfiguration | j = k ∨
          ¬(deletedOpenGraph ω v).Reachable (ys j) (ys k)} =
          {ω : LatticeConfiguration | (deletedOpenGraph ω v).Reachable (ys j) (ys k)}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, hjk, false_or]
      rw [heq]
      exact (measurableSet_deleted_reachable v (ys j) (ys k)).compl
  have h := MeasurableSet.iUnion fun ys : Fin 3 → LatticeVertex =>
    let hleft := MeasurableSet.iInter fun j =>
      (measurableSet_open_adj v (ys j)).inter (measurableSet_deletedInfiniteAt v (ys j))
    let hright := MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => hsep ys j k
    hleft.inter hright
  convert h using 1
  ext ω
  simp only [isTrifurcationAt, mem_ofPred_eq, mem_iUnion, mem_iInter,
    mem_inter_iff, imp_iff_not_or, not_not]

end
end PottsContinuity.PD.RCInfinite
