-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxFirstHitCandidateLift.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxFinitePolygonCandidates
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open SimpleGraph

def slitBoxUnderlyingToSquareHom (n : ℕ) :
    slitBoxGraph n →g squareLattice where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    exact (slitBoxGraph_adj_iff n a b).mp hab |>.1

def slitBoxInduceToRectangleHom (n : ℕ) :
    squareLattice.induce
        (latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) : Set LatticeVertex) →g
      rectangleGraph (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) where
  toFun := fun z => ⟨z.val, z.property⟩
  map_rel' := by
    intro a b hab
    exact (rectangleGraph_adj_iff _ _ _ _ _).2 hab

/-- A bounded actual square-lattice first-hit path lifts to the literal slit
graph while preserving its complete ordered walk. -/
theorem slitBoxFirstHitCandidate_of_bounded_first_hit_walk
    (n : ℕ) (u t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    (w : squareLattice.Walk u.val t.val) (hw : w.IsPath)
    (hbox : ∀ z ∈ w.support,
      z ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n))
    (hfirst : ∀ z ∈ w.support,
      (z.1 = 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ n) → z = t.val) :
    ∃ r : SlitBoxFirstHitBaseCandidates n u,
      ∃ hrt : r.val.1 = t,
        ((r.val.2 : (slitBoxGraph n).Walk u r.val.1).map
          (slitBoxUnderlyingToSquareHom n)).copy rfl (congrArg Subtype.val hrt) = w := by
  classical
  let box : Set LatticeVertex :=
    latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)
  let wBox : (squareLattice.induce box).Walk
      ⟨u.val, hbox u.val w.start_mem_support⟩ ⟨t.val, hbox t.val w.end_mem_support⟩ :=
    w.induce box hbox
  have hwBoxMap : wBox.map (Embedding.induce box).toHom = w := by
    simp [wBox]
  have hsupportMap : wBox.support.map (fun z => z.val) = w.support := by
    have h := congrArg SimpleGraph.Walk.support hwBoxMap
    rw [SimpleGraph.Walk.support_map] at h
    change wBox.support.map (fun z => z.val) = w.support at h
    exact h
  let wRect := wBox.map (slitBoxInduceToRectangleHom n)
  have hsupportRect : wRect.support.map (fun z : SlitBoxVertex n => z.val) = w.support := by
    calc
      wRect.support.map (fun z : SlitBoxVertex n => z.val) =
          wBox.support.map (fun z => z.val) := by
        simp [wRect, slitBoxInduceToRectangleHom]
      _ = w.support := hsupportMap
  have hrectEdgeToSlit : ∀ e, e ∈ wRect.edges → e ∈ (slitBoxGraph n).edgeSet := by
    intro e he
    obtain ⟨⟨a, b⟩, habPair⟩ := Sym2.mk_surjective e
    have he' : s(a, b) ∈ wRect.edges := by
      rw [← habPair] at he
      exact he
    have hadjRect : (rectangleGraph (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)).Adj a b :=
      (rectangleGraph (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)).mem_edgeSet.mp
        (wRect.edges_subset_edgeSet he')
    have hsq : squareLattice.Adj a.val b.val :=
      (rectangleGraph_adj_iff _ _ _ _ _).mp hadjRect
    have haW : a.val ∈ w.support := by
      have hmem := wRect.fst_mem_support_of_mem_edges he'
      have : a.val ∈ wRect.support.map (fun z => z.val) :=
        List.mem_map.mpr ⟨a, hmem, rfl⟩
      simpa [hsupportRect] using this
    have hbW : b.val ∈ w.support := by
      have hmem := wRect.snd_mem_support_of_mem_edges he'
      have : b.val ∈ wRect.support.map (fun z => z.val) :=
        List.mem_map.mpr ⟨b, hmem, rfl⟩
      simpa [hsupportRect] using this
    have hnotBoth : ¬ (a ∈ slitBoxWiredArc n ∧ b ∈ slitBoxWiredArc n) := by
      intro hab
      have haEq := hfirst a.val haW ((mem_slitBoxWiredArc_iff n a).mp hab.1)
      have hbEq := hfirst b.val hbW ((mem_slitBoxWiredArc_iff n b).mp hab.2)
      rw [haEq, hbEq] at hsq
      exact squareLattice.loopless.irrefl t.val hsq
    have hslit : s(a, b) ∈ (slitBoxGraph n).edgeSet := (slitBoxGraph n).mem_edgeSet.mpr
      ((slitBoxGraph_adj_iff n a b).2 ⟨hsq, by
        intro hcoords
        exact hnotBoth ⟨(mem_slitBoxWiredArc_iff n a).2 hcoords.1,
          (mem_slitBoxWiredArc_iff n b).2 hcoords.2⟩⟩)
    rw [← habPair]
    exact hslit
  let path : (slitBoxGraph n).Walk u t :=
    wRect.transfer (slitBoxGraph n) hrectEdgeToSlit
  have hpathSupport : path.support = wRect.support := by
    exact SimpleGraph.Walk.support_transfer (p := wRect)
      (H := slitBoxGraph n) hrectEdgeToSlit
  have hpathMappedSupport :
      ((path.map (slitBoxUnderlyingToSquareHom n)).copy rfl rfl).support = w.support := by
    calc
      ((path.map (slitBoxUnderlyingToSquareHom n)).copy rfl rfl).support =
          (path.map (slitBoxUnderlyingToSquareHom n)).support := by
        rw [SimpleGraph.Walk.support_copy]
      _ = path.support.map (slitBoxUnderlyingToSquareHom n) := by
        rw [SimpleGraph.Walk.support_map]
      _ = w.support := by
        rw [hpathSupport]
        exact hsupportRect
  have hmap : (path.map (slitBoxUnderlyingToSquareHom n)).copy rfl rfl = w :=
    SimpleGraph.Walk.ext_support hpathMappedSupport
  have hpath : path.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    have htargetNodup : List.Nodup (path.support.map
        (slitBoxUnderlyingToSquareHom n)) := by
      have h := congrArg SimpleGraph.Walk.support hmap
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at h
      exact h ▸ hw.support_nodup
    have hinj : Function.Injective (slitBoxUnderlyingToSquareHom n) := by
      intro a b hab
      exact Subtype.ext hab
    exact List.Nodup.of_map _ htargetNodup
  have hfirst' : ∀ v ∈ finiteSimplePathSupport ⟨t, ⟨path, hpath⟩⟩,
      v ∈ slitBoxWiredArc n → v = t := by
    intro v hv hvArc
    have hvW : v.val ∈ w.support := by
      have hvPath : v ∈ path.support := by
        simpa [finiteSimplePathSupport] using hv
      have hvRect : v ∈ wRect.support := by
        simpa [path, hpathSupport] using hvPath
      have : v.val ∈ wRect.support.map (fun z => z.val) :=
        List.mem_map.mpr ⟨v, hvRect, rfl⟩
      simpa [hsupportRect] using this
    have hval := hfirst v.val hvW ((mem_slitBoxWiredArc_iff n v).mp hvArc)
    exact Subtype.ext hval
  let candidate : SlitBoxFirstHitBaseCandidates n u :=
    ⟨⟨t, ⟨path, hpath⟩⟩, ht, hfirst'⟩
  exact ⟨candidate, rfl, hmap⟩

end PottsContinuity.FKC.FiniteFK
