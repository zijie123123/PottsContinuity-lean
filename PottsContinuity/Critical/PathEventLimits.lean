module

public import PottsContinuity.Critical.ThresholdMonotonicity
public import PottsContinuity.PD.FK.FrozenLimitBridge
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Critical

open MeasureTheory
open Filter Topology
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

/-- The finite set of all lattice edges that can occur in a length-`n`
direction code starting at the origin. -/
def walkCodeSupport (n : ℕ) : Finset LatticeEdge :=
  Finset.univ.biUnion fun c : WalkCode n => walkCodeEdgeFinset (0, 0) c

private theorem walk_edge_mem_walkCodeSupport {y : LatticeVertex}
    (p : squareLattice.Walk (0, 0) y) (e : LatticeEdge)
    (he : e.val ∈ p.edges) : e ∈ walkCodeSupport p.length := by
  let c := walkCodeOfWalk p
  apply Finset.mem_biUnion.mpr
  refine ⟨c, Finset.mem_univ _, ?_⟩
  unfold walkCodeEdgeFinset
  apply List.mem_toFinset.mpr
  have hmap : e.val ∈
      (walkCodeEdgeList (0, 0) c.toList).map Subtype.val := by
    rw [walkCodeEdgeList_val_ofWalk]
    exact he
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hmap
  have hfe' : f = e := by
    apply Subtype.ext
    exact hfe
  simpa [hfe'] using hf

/-- The event that the origin has a simple open path of length `n`. -/
def simpleOpenWalkCylinder (n : ℕ) : Set LatticeConfiguration :=
  {ω | (fun e => ω e = true) ∈ openSimpleWalkEvent (0, 0) n}

private theorem simpleOpenWalkCylinder_depends_on_walkCodeSupport (n : ℕ)
    {ω ω' : LatticeConfiguration}
    (hagree : ∀ e ∈ walkCodeSupport n, ω e = ω' e) :
    ω ∈ simpleOpenWalkCylinder n ↔ ω' ∈ simpleOpenWalkCylinder n := by
  constructor
  · rintro ⟨y, p, hp, hlen, hopen⟩
    refine ⟨y, p, hp, hlen, ?_⟩
    intro e he
    have hsupp : e ∈ walkCodeSupport n := by
      simpa [hlen] using walk_edge_mem_walkCodeSupport p e he
    exact (hagree e hsupp).symm.trans (hopen e he)
  · rintro ⟨y, p, hp, hlen, hopen⟩
    refine ⟨y, p, hp, hlen, ?_⟩
    intro e he
    have hsupp : e ∈ walkCodeSupport n := by
      simpa [hlen] using walk_edge_mem_walkCodeSupport p e he
    exact (hagree e hsupp).trans (hopen e he)

/-- Any event determined by a finite set of edge coordinates is clopen in the
whole-lattice product topology. -/
private theorem isClopen_of_finite_edge_support (A : Finset LatticeEdge)
    (E : Set LatticeConfiguration)
    (hdep : ∀ ω ω', (∀ e ∈ A, ω e = ω' e) → (ω ∈ E ↔ ω' ∈ E)) :
    IsClopen E := by
  classical
  let extension (f : {e : LatticeEdge // e ∈ A} → Bool) : LatticeConfiguration :=
    fun e => if h : e ∈ A then f ⟨e, h⟩ else false
  let selected := {f : {e : LatticeEdge // e ∈ A} → Bool // extension f ∈ E}
  have hextension (f : {e : LatticeEdge // e ∈ A} → Bool) {e : LatticeEdge}
      (he : e ∈ A) : extension f e = f ⟨e, he⟩ := by
    simp [extension, he]
  have hEq : E = ⋃ f : selected, patternCylinder A (extension f.1) := by
    ext ω
    constructor
    · intro hω
      let f : {e : LatticeEdge // e ∈ A} → Bool := fun e => ω e
      have hfE : extension f ∈ E := by
        apply (hdep ω (extension f) ?_).mp hω
        intro e he
        exact (hextension f he).symm
      refine Set.mem_iUnion.mpr ⟨⟨f, hfE⟩, ?_⟩
      intro e he
      exact (hextension f he).symm
    · intro hω
      obtain ⟨f, hpattern⟩ := Set.mem_iUnion.mp hω
      apply (hdep ω (extension f.1) ?_).mpr f.2
      intro e he
      exact hpattern e he
  rw [hEq]
  apply isClopen_iUnion_of_finite
  intro f
  exact patternCylinder_isClopen A (extension f.1)

theorem simpleOpenWalkCylinder_isClopen (n : ℕ) :
    IsClopen (simpleOpenWalkCylinder n) := by
  apply isClopen_of_finite_edge_support (walkCodeSupport n)
  intro ω ω' hagree
  exact simpleOpenWalkCylinder_depends_on_walkCodeSupport n hagree

theorem simpleOpenWalkCylinder_isIncreasing (n : ℕ) :
    IsIncreasingConfigurationEvent (simpleOpenWalkCylinder n) := by
  intro ω ω' hωω' hω
  rcases hω with ⟨y, p, hp, hlen, hopen⟩
  refine ⟨y, p, hp, hlen, ?_⟩
  intro e he
  exact hωω' e (hopen e he)

theorem infiniteAt_subset_simpleOpenWalkCylinder (n : ℕ) :
    infiniteAt (0, 0) ⊆ simpleOpenWalkCylinder n := by
  intro ω hω
  exact infiniteAt_subset_openSimpleWalkEvent n hω

private theorem squarePath_to_openGraph {x y : LatticeVertex}
    (ω : LatticeConfiguration) (p : squareLattice.Walk x y) (hp : p.IsPath)
    (hopen : ∀ e : LatticeEdge, e.val ∈ p.edges → ω e = true) :
    ∃ q : (PD.rcInfiniteOpenGraph ω).Walk x y,
      q.IsPath ∧ q.support = p.support := by
  induction p with
  | nil => exact ⟨.nil, by simp, rfl⟩
  | @cons x z y h p ih =>
      have hp' : p.IsPath ∧ x ∉ p.support :=
        (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
      have hEdge : s(x, z) ∈ squareLattice.edgeSet := squareLattice.mem_edgeSet.mpr h
      let e : LatticeEdge := ⟨s(x, z), hEdge⟩
      have he : e.val ∈ (SimpleGraph.Walk.cons h p).edges := by
        change s(x, z) ∈ (SimpleGraph.Walk.cons h p).edges
        simp
      have hopenHead : ω e = true := hopen e he
      have hAdj : (PD.rcInfiniteOpenGraph ω).Adj x z :=
        (rcInfiniteOpenGraph_adj ω x z).mpr ⟨hEdge, hopenHead⟩
      obtain ⟨q, hq, hqSupport⟩ := ih hp'.1 (by
        intro f hf
        apply hopen f
        exact List.mem_cons_of_mem _ hf)
      have hxnot : x ∉ q.support := by simpa [hqSupport] using hp'.2
      refine ⟨SimpleGraph.Walk.cons hAdj q, ?_, ?_⟩
      · exact (SimpleGraph.Walk.cons_isPath_iff hAdj q).mpr ⟨hq, hxnot⟩
      · simp [hqSupport]

private theorem walk_support_reachable {V : Type*} {G : SimpleGraph V}
    {x y : V} (p : G.Walk x y) :
    ∀ z ∈ p.support, G.Reachable x z := by
  induction p with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact .refl _
  | @cons x v y h p ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact .refl _
      · exact h.reachable.trans (ih z hz)

/-- A configuration has an infinite origin cluster exactly when it admits
simple open paths from the origin of every finite length. -/
theorem infiniteAt_eq_iInter_simpleOpenWalkCylinder :
    infiniteAt (0, 0) = ⋂ n : ℕ, simpleOpenWalkCylinder n := by
  ext ω
  constructor
  · intro hω
    exact Set.mem_iInter.mpr fun n => infiniteAt_subset_simpleOpenWalkCylinder n hω
  · intro hω
    change (cluster ω (0, 0)).Infinite
    by_contra hnot
    have hfinite : (cluster ω (0, 0)).Finite := not_not.mp hnot
    let n := hfinite.toFinset.card
    have hpath := (Set.mem_iInter.mp hω) n
    obtain ⟨y, p, hp, hlen, hopen⟩ := hpath
    obtain ⟨q, hq, hqSupport⟩ := squarePath_to_openGraph ω p hp hopen
    have hsub : q.support.toFinset ⊆ hfinite.toFinset := by
      intro z hz
      apply hfinite.mem_toFinset.mpr
      have hzq : z ∈ q.support := List.mem_toFinset.mp hz
      change (PD.rcInfiniteOpenGraph ω).Reachable (0, 0) z
      exact walk_support_reachable q z hzq
    have hqLen : q.length = n := by
      have hlenSupport := congrArg List.length hqSupport
      rw [q.length_support, p.length_support, hlen] at hlenSupport
      exact Nat.add_right_cancel hlenSupport
    have hcard : q.support.toFinset.card = n + 1 := by
      rw [List.toFinset_card_of_nodup hq.support_nodup,
        q.length_support, hqLen]
    have hle := Finset.card_le_card hsub
    dsimp [n] at hcard hle
    omega

theorem simpleOpenWalkCylinder_succ_subset (n : ℕ) :
    simpleOpenWalkCylinder (n + 1) ⊆ simpleOpenWalkCylinder n := by
  intro ω hω
  obtain ⟨y, p, hp, hlen, hopen⟩ := hω
  have hdrop : p.dropLast.IsPath := hp.dropLast
  have hdropLen : p.dropLast.length = n := by simp [hlen]
  refine ⟨p.penultimate, p.dropLast, hdrop, hdropLen, ?_⟩
  intro e he
  apply hopen e
  rw [SimpleGraph.Walk.edges_dropLast] at he
  exact List.mem_of_mem_dropLast he

private theorem simpleOpenWalkCylinder_antitone :
    Antitone simpleOpenWalkCylinder := by
  intro m n hmn
  induction hmn with
  | refl => exact Set.Subset.rfl
  | @step n h ih =>
      exact (simpleOpenWalkCylinder_succ_subset n).trans ih

/-- Any two wired box limits at ordered parameters have ordered infinite
origin-cluster probabilities. -/
theorem wiredBoxLimit_infiniteAt_parameter_mono (θ θ' : Parameters)
    (hq : θ.val = θ'.val) (hp : edgeParameter θ ≤ edgeParameter θ')
    (μ ν : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (hν : Tendsto (fun n => wiredBoxProbabilityMeasure θ' (0, 0) n) atTop (𝓝 ν)) :
    (μ : Measure LatticeConfiguration) (infiniteAt (0, 0)) ≤
      (ν : Measure LatticeConfiguration) (infiniteAt (0, 0)) := by
  have hpoint (n : ℕ) :
      (μ : Measure LatticeConfiguration) (simpleOpenWalkCylinder n) ≤
        (ν : Measure LatticeConfiguration) (simpleOpenWalkCylinder n) := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ENNReal.coe_le_coe.mpr
      (wiredBoxLimit_parameter_mono_of_clopen θ θ' hq hp μ ν hμ hν
        (simpleOpenWalkCylinder n) (simpleOpenWalkCylinder_isClopen n)
        (simpleOpenWalkCylinder_isIncreasing n))
  have hμiInter :
      (μ : Measure LatticeConfiguration) (⋂ n, simpleOpenWalkCylinder n) =
        ⨅ n, (μ : Measure LatticeConfiguration) (simpleOpenWalkCylinder n) :=
    simpleOpenWalkCylinder_antitone.measure_iInter
      (fun n => (simpleOpenWalkCylinder_isClopen n).1.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have hνiInter :
      (ν : Measure LatticeConfiguration) (⋂ n, simpleOpenWalkCylinder n) =
        ⨅ n, (ν : Measure LatticeConfiguration) (simpleOpenWalkCylinder n) :=
    simpleOpenWalkCylinder_antitone.measure_iInter
      (fun n => (simpleOpenWalkCylinder_isClopen n).1.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  rw [infiniteAt_eq_iInter_simpleOpenWalkCylinder, hμiInter, hνiInter]
  exact iInf_mono hpoint

end
end PottsContinuity.Critical
