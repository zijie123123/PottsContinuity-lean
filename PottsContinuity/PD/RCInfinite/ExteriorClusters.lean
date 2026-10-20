-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/ExteriorClusters.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.FiniteBoxCounting
public import PottsContinuity.PD.RCInfinite.GraphModification
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- The open graph after deleting every edge incident to the centered box. -/
def exteriorOpenGraph (ω : LatticeConfiguration) (n : ℕ) : SimpleGraph LatticeVertex :=
  (rcInfiniteOpenGraph ω).deleteEdges
    (⋃ v ∈ (latticeBox (0, 0) n : Set LatticeVertex), squareLattice.incidenceSet v)

theorem exteriorOpenGraph_adj (ω : LatticeConfiguration) (n : ℕ)
    (x y : LatticeVertex) :
    (exteriorOpenGraph ω n).Adj x y ↔
      (rcInfiniteOpenGraph ω).Adj x y ∧ x ∉ latticeBox (0, 0) n ∧
        y ∉ latticeBox (0, 0) n := by
  rw [exteriorOpenGraph, SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hOpen, hcut⟩
    refine ⟨hOpen, ?_, ?_⟩
    · intro hx
      apply hcut
      refine Set.mem_iUnion.mpr ⟨x, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hx, ?_⟩
      rw [SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨squareLattice.mem_edgeSet.mp ((rcInfiniteOpenGraph_adj ω x y).mp hOpen).1,
        Or.inl rfl⟩
    · intro hy
      apply hcut
      refine Set.mem_iUnion.mpr ⟨y, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hy, ?_⟩
      rw [SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨squareLattice.mem_edgeSet.mp ((rcInfiniteOpenGraph_adj ω x y).mp hOpen).1,
        Or.inr rfl⟩
  · rintro ⟨hOpen, hx, hy⟩
    refine ⟨hOpen, ?_⟩
    intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨v, hv, hinc⟩ := hmem
    rw [SimpleGraph.mk'_mem_incidenceSet_iff] at hinc
    rcases hinc.2 with heq | heq
    · exact hx (heq ▸ hv)
    · exact hy (heq ▸ hv)

theorem exteriorOpenGraph_le (ω : LatticeConfiguration) (n : ℕ) :
    exteriorOpenGraph ω n ≤ rcInfiniteOpenGraph ω := by
  intro x y h
  exact (exteriorOpenGraph_adj ω n x y).mp h |>.1

theorem lattice_adj_box_succ {n : ℕ} {x y : LatticeVertex}
    (hxy : squareLattice.Adj x y) (hx : x ∈ latticeBox (0, 0) n) :
    y ∈ latticeBox (0, 0) (n + 1) := by
  rw [mem_latticeBox] at hx ⊢
  simp only at hx ⊢
  rcases (squareLattice_adj_iff x y).mp hxy with ⟨horiz, vert⟩ | ⟨horiz, vert⟩
  · rcases horiz with hstep | hstep <;> omega
  · rcases vert with hstep | hstep <;> omega

local instance boxEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _

def boxIncidentEdges (n : ℕ) : Finset Edge :=
  ((Finset.univ : Finset (boxGraph (0, 0) (n + 1)).edgeSet).map
    (boxEdgeEmbedding (0, 0) (n + 1))).filter
      (fun e => ∃ v ∈ latticeBox (0, 0) n, v ∈ e.val)

theorem mem_boxIncidentEdges (n : ℕ) (e : Edge) :
    e ∈ boxIncidentEdges n ↔
      e ∈ boxEdges (0, 0) (n + 1) ∧
        ∃ v ∈ latticeBox (0, 0) n, v ∈ e.val := by
  constructor
  · intro he
    obtain ⟨hemap, hincident⟩ := Finset.mem_filter.mp he
    obtain ⟨f, _, heq⟩ := Finset.mem_map.mp hemap
    exact ⟨⟨f, heq⟩, hincident⟩
  · rintro ⟨⟨f, heq⟩, hincident⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_map.mpr ⟨f, Finset.mem_univ f, heq⟩, hincident⟩

theorem edge_incident_box_mem_boxIncidentEdges (n : ℕ) (e : Edge)
    (hincident : ∃ v ∈ latticeBox (0, 0) n, v ∈ e.val) :
    e ∈ boxIncidentEdges n := by
  apply (mem_boxIncidentEdges n e).2
  refine ⟨?_, hincident⟩
  rw [mem_boxEdges_iff]
  intro x hx
  obtain ⟨v, hv, hvEdge⟩ := hincident
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hva : v = a ∨ v = b := by simpa using hvEdge
    have hab : squareLattice.Adj a b := squareLattice.mem_edgeSet.mp he
    rcases hva with hav | hvb
    · subst v
      rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
      · exact latticeBox_mono (0, 0) (by omega) hv
      · exact lattice_adj_box_succ hab hv
    · subst v
      rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
      · exact lattice_adj_box_succ hab.symm hv
      · exact latticeBox_mono (0, 0) (by omega) hv

def exteriorChain : ℕ → LatticeConfiguration → ℕ → LatticeVertex → LatticeVertex → Prop
  | 0, _, _, x, y => x = y
  | k + 1, ω, n, x, y =>
      ∃ z, (exteriorOpenGraph ω n).Adj x z ∧ exteriorChain k ω n z y

theorem exteriorChain_reachable {k : ℕ} {ω : LatticeConfiguration} {n : ℕ}
    {x y : LatticeVertex} (h : exteriorChain k ω n x y) :
    (exteriorOpenGraph ω n).Reachable x y := by
  induction k generalizing x with
  | zero => exact h ▸ SimpleGraph.Reachable.refl x
  | succ k ih =>
    obtain ⟨z, hxz, hzy⟩ := h
    exact hxz.reachable.trans (ih hzy)

theorem exterior_reachable_iff_chain (ω : LatticeConfiguration) (n : ℕ)
    (x y : LatticeVertex) :
    (exteriorOpenGraph ω n).Reachable x y ↔ ∃ k, exteriorChain k ω n x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨0, rfl⟩
    | cons h w ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, _, h, hk⟩
  · rintro ⟨k, hk⟩
    exact exteriorChain_reachable hk

theorem measurableSet_exteriorAdj (n : ℕ) (x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | (exteriorOpenGraph ω n).Adj x y} := by
  have hfixed : MeasurableSet {ω : LatticeConfiguration |
      x ∉ latticeBox (0, 0) n ∧ y ∉ latticeBox (0, 0) n} := by
    by_cases hx : x ∈ latticeBox (0, 0) n <;>
      by_cases hy : y ∈ latticeBox (0, 0) n <;> simp [hx, hy]
  have heq : {ω : LatticeConfiguration | (exteriorOpenGraph ω n).Adj x y} =
      {ω | (rcInfiniteOpenGraph ω).Adj x y} ∩
        {ω | x ∉ latticeBox (0, 0) n ∧ y ∉ latticeBox (0, 0) n} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact exteriorOpenGraph_adj ω n x y
  rw [heq]
  exact (measurableSet_open_adj x y).inter hfixed

theorem measurableSet_exteriorReachable (n : ℕ) (x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | (exteriorOpenGraph ω n).Reachable x y} := by
  have h k : MeasurableSet {ω : LatticeConfiguration | exteriorChain k ω n x y} := by
    induction k generalizing x with
    | zero => by_cases hxy : x = y <;> simp [exteriorChain, hxy]
    | succ k ih =>
      have h := MeasurableSet.iUnion fun z : LatticeVertex =>
        (measurableSet_exteriorAdj n x z).inter (ih z)
      convert h using 1
      ext ω
      simp [exteriorChain]
  have h := MeasurableSet.iUnion h
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, exterior_reachable_iff_chain, mem_iUnion]

/-- An infinite component of the graph outside a box, expressed by escape from
every finite set of vertices. -/
def exteriorInfiniteAt (n : ℕ) (x : LatticeVertex) : Set LatticeConfiguration :=
  {ω | ∀ F : Finset LatticeVertex, ∃ y, y ∉ F ∧
    (exteriorOpenGraph ω n).Reachable x y}

theorem measurableSet_exteriorInfiniteAt (n : ℕ) (x : LatticeVertex) :
    MeasurableSet (exteriorInfiniteAt n x) := by
  have hinner (F : Finset LatticeVertex) : MeasurableSet
      (⋃ y : {y : LatticeVertex // y ∉ F},
        {ω : LatticeConfiguration | (exteriorOpenGraph ω n).Reachable x y.val}) :=
    MeasurableSet.iUnion fun y => measurableSet_exteriorReachable n x y.val
  have h := MeasurableSet.iInter hinner
  convert h using 1
  ext ω
  simp only [exteriorInfiniteAt, mem_ofPred_eq, mem_iInter, mem_iUnion,
    Subtype.exists, exists_prop]

theorem exteriorInfiniteAt_iff_infinite (ω : LatticeConfiguration) (n : ℕ)
    (x : LatticeVertex) :
    ω ∈ exteriorInfiniteAt n x ↔
      {y | (exteriorOpenGraph ω n).Reachable x y}.Infinite := by
  constructor
  · intro h hfin
    obtain ⟨y, hyF, hreach⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.mpr hreach)
  · intro h F
    obtain ⟨y, hy, hyF⟩ := h.exists_notMem_finset F
    exact ⟨y, hyF, hy⟩

theorem walk_reachable_exterior {ω : LatticeConfiguration} {n : ℕ}
    {x y : LatticeVertex} (w : (rcInfiniteOpenGraph ω).Walk x y)
    (havoid : ∀ z, z ∈ w.support → z ∉ latticeBox (0, 0) n) :
    (exteriorOpenGraph ω n).Reachable x y := by
  induction w with
  | nil => exact .refl _
  | @cons x y z h w ih =>
    have hx := havoid x (by simp)
    have hy := havoid y (List.mem_cons_of_mem _ w.start_mem_support)
    have htail (a : LatticeVertex) (ha : a ∈ w.support) :
        a ∉ latticeBox (0, 0) n := havoid a (List.mem_cons_of_mem _ ha)
    exact ((exteriorOpenGraph_adj ω n x y).mpr ⟨h, hx, hy⟩).reachable.trans
      (ih htail)

/-- Every infinite open cluster meeting a finite box has an infinite open
component outside that box, reached by an open edge crossing its boundary. -/
theorem infiniteAt_has_exterior_exit (ω : LatticeConfiguration) (n : ℕ)
    (x : LatticeVertex) (hx : x ∈ latticeBox (0, 0) n)
    (hinf : ω ∈ infiniteAt x) :
    ∃ inside outside : LatticeVertex,
      ∃ he : s(inside, outside) ∈ squareLattice.edgeSet,
      inside ∈ latticeBox (0, 0) n ∧ outside ∉ latticeBox (0, 0) n ∧
      ω ⟨s(inside, outside), he⟩ = true ∧
      (rcInfiniteOpenGraph ω).Reachable x outside ∧
      ω ∈ exteriorInfiniteAt n outside := by
  have hGH : exteriorOpenGraph ω n ≤ rcInfiniteOpenGraph ω := exteriorOpenGraph_le ω n
  have hnew : ∀ a b, (rcInfiniteOpenGraph ω).Adj a b →
      ¬(exteriorOpenGraph ω n).Adj a b →
      a ∈ latticeBox (0, 0) (n + 1) ∧ b ∈ latticeBox (0, 0) (n + 1) := by
    intro a b hab hnot
    have hadj : squareLattice.Adj a b :=
      squareLattice.mem_edgeSet.mp ((rcInfiniteOpenGraph_adj ω a b).mp hab).1
    have hinside : a ∈ latticeBox (0, 0) n ∨ b ∈ latticeBox (0, 0) n := by
      by_contra hn
      apply hnot
      exact (exteriorOpenGraph_adj ω n a b).mpr
        ⟨hab, (not_or.mp hn).1, (not_or.mp hn).2⟩
    rcases hinside with ha | hb
    · exact ⟨latticeBox_mono (0, 0) (by omega) ha, lattice_adj_box_succ hadj ha⟩
    · exact ⟨lattice_adj_box_succ hadj.symm hb,
        latticeBox_mono (0, 0) (by omega) hb⟩
  have hinf' : {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite := by
    change (cluster ω x).Infinite at hinf
    exact hinf
  obtain ⟨z, hOrigXZ, hzinf⟩ :=
    infinite_component_contains_old hGH (latticeBox (0, 0) (n + 1)) hnew x hinf'
  have hzinf : ω ∈ exteriorInfiniteAt n z :=
    (exteriorInfiniteAt_iff_infinite ω n z).mpr hzinf
  have hzout : z ∉ latticeBox (0, 0) n := by
    intro hzin
    obtain ⟨y, hy, hzy⟩ := hzinf {z}
    have hzeq : y = z := by
      obtain ⟨w⟩ := hzy
      cases w with
      | nil => rfl
      | cons h _ =>
        exact False.elim (((exteriorOpenGraph_adj ω n z _).mp h).2.1 hzin)
    exact hy (by simp [hzeq])
  have hOrigXZKeep := hOrigXZ
  obtain ⟨w⟩ := hOrigXZ
  let S : Set LatticeVertex := {y | y ∉ latticeBox (0, 0) n}
  have hzS : z ∈ S := hzout
  have hxNotS : x ∉ S := by simpa [S] using hx
  obtain ⟨outside, hout, p, hp, inside, hin, houtin⟩ :=
    walk_prefix_to_boundary (S := S) w.reverse hzS hxNotS
  have hout' : outside ∉ latticeBox (0, 0) n := by simpa [S] using hout
  have houtin' : inside ∈ latticeBox (0, 0) n := by simpa [S] using houtin
  have hp' (a : LatticeVertex) (ha : a ∈ p.support) :
      a ∉ latticeBox (0, 0) n := by simpa [S] using hp a ha
  have hreachOutside : (exteriorOpenGraph ω n).Reachable z outside :=
    walk_reachable_exterior p hp'
  have houtInf : ω ∈ exteriorInfiniteAt n outside := by
    rw [exteriorInfiniteAt_iff_infinite] at hzinf ⊢
    have heq : {y | (exteriorOpenGraph ω n).Reachable outside y} =
        {y | (exteriorOpenGraph ω n).Reachable z y} := by
      ext y
      constructor
      · intro h
        exact hreachOutside.trans h
      · intro h
        exact hreachOutside.symm.trans h
    rw [heq]
    exact hzinf
  have hin' : (rcInfiniteOpenGraph ω).Adj outside inside := hin
  obtain ⟨he, _hopen⟩ := (rcInfiniteOpenGraph_adj ω outside inside).mp hin'
  have he' : s(inside, outside) ∈ squareLattice.edgeSet := by
    exact squareLattice.mem_edgeSet.mpr (squareLattice.mem_edgeSet.mp he).symm
  have heState : ω ⟨s(inside, outside), he'⟩ = true := by
    have hsymm : (rcInfiniteOpenGraph ω).Adj inside outside := hin'.symm
    exact ((rcInfiniteOpenGraph_adj ω inside outside).mp hsymm).2
  have hreachXoutside : (rcInfiniteOpenGraph ω).Reachable x outside :=
    SimpleGraph.Reachable.trans hOrigXZKeep (hreachOutside.mono hGH)
  refine ⟨inside, outside, he', houtin', hout', heState, hreachXoutside, houtInf⟩

end
end PottsContinuity.PD.RCInfinite
