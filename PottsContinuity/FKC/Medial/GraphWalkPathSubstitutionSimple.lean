-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/GraphWalkPathSubstitutionSimple.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.GraphWalkPathSubstitution
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

private theorem graphWalkSubstitute_support_tail {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} (p : G.Walk u v) :
    (graphWalkSubstitute G H f route p).support.tail =
      p.darts.flatMap fun d => (route d.adj).support.tail := by
  induction p with
  | nil => simp [graphWalkSubstitute]
  | cons h p ih =>
      rw [graphWalkSubstitute_cons, SimpleGraph.Walk.tail_support_append,
        SimpleGraph.Walk.darts_cons, List.flatMap_cons, ih]

private theorem path_dart_snd_ne_start {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) {d : G.Dart}
    (hd : d ∈ p.darts) : u ≠ d.snd := by
  have htail : d.snd ∈ p.support.tail := by
    rw [← SimpleGraph.Walk.map_snd_darts p]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  have hstart : u ∉ p.support.tail := by
    have hnd := hp.support_nodup
    rw [← SimpleGraph.Walk.cons_tail_support p] at hnd
    exact (List.nodup_cons.mp hnd).1
  intro heq
  exact hstart (heq ▸ htail)

private theorem path_dart_edge_injective {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    ∀ {d₁ d₂ : G.Dart}, d₁ ∈ p.darts → d₂ ∈ p.darts →
      d₁.edge = d₂.edge → d₁ = d₂ := by
  have hdarts : p.darts.Nodup :=
    SimpleGraph.Walk.darts_nodup_of_support_nodup hp.support_nodup
  have hedges : (p.darts.map fun d : G.Dart => d.edge).Nodup := by
    simpa [SimpleGraph.Walk.edges] using hp.edges_nodup
  intro d₁ d₂ hd₁ hd₂ he
  exact (List.nodup_map_iff_inj_on hdarts).mp hedges d₁ hd₁ d₂ hd₂ he

private theorem graphWalkRouteTail_getLast {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {a b : V} (h : G.Adj a b) :
    ∃ hne : (route h).support.tail ≠ [],
      (route h).support.tail.getLast hne = f b := by
  have hpositive : 0 < (route h).length := by
    by_contra hnot
    have hzero : (route h).length = 0 := by omega
    have heq : f a = f b := SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact h.ne (hf heq)
  have htailLength : (route h).support.tail.length = (route h).length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  have hne : (route h).support.tail ≠ [] := by
    intro hnil
    have hlenZero : (route h).support.tail.length = 0 := by simp [hnil]
    rw [htailLength] at hlenZero
    omega
  refine ⟨hne, ?_⟩
  have hnotnil : ¬ (route h).Nil := by
    intro hnil
    have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    omega
  simp

private theorem graphWalkRouteTails_disjoint_of_interiors {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    (hrouteRange : ∀ {u v : V} (h : G.Adj u v) {z : W},
      z ∈ (route h).support.tail → z ∈ Set.range f → z = f v)
    (hinteriorDisjoint : ∀ {a b c d : V} (h₁ : G.Adj a b) (h₂ : G.Adj c d),
      s(a,b) ≠ s(c,d) →
        List.Disjoint ((route h₁).support.tail.dropLast)
          ((route h₂).support.tail.dropLast))
    {a b c d : V} (h₁ : G.Adj a b) (h₂ : G.Adj c d)
    (hedge : s(a,b) ≠ s(c,d)) (htarget : b ≠ d) :
    List.Disjoint ((route h₁).support.tail) ((route h₂).support.tail) := by
  obtain ⟨hne₁, hlast₁⟩ :=
    graphWalkRouteTail_getLast G H f hf route h₁
  obtain ⟨hne₂, hlast₂⟩ :=
    graphWalkRouteTail_getLast G H f hf route h₂
  apply List.disjoint_left.mpr
  intro z hz₁ hz₂
  by_cases hzr : z ∈ Set.range f
  · have hz₁' := hrouteRange h₁ hz₁ hzr
    have hz₂' := hrouteRange h₂ hz₂ hzr
    exact htarget (hf (hz₁'.symm.trans hz₂'))
  · have hinter₁ : z ∈ (route h₁).support.tail.dropLast := by
      apply List.mem_dropLast_of_mem_of_ne_getLast hz₁
      intro heq
      apply hzr
      exact ⟨b, (heq.trans hlast₁).symm⟩
    have hinter₂ : z ∈ (route h₂).support.tail.dropLast := by
      apply List.mem_dropLast_of_mem_of_ne_getLast hz₂
      intro heq
      apply hzr
      exact ⟨d, (heq.trans hlast₂).symm⟩
    exact (List.disjoint_left.mp (hinteriorDisjoint h₁ h₂ hedge) hinter₁) hinter₂

private theorem graphWalkSubstitute_route_tails_pairwise {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    (hf : Function.Injective f)
    (hrouteRange : ∀ {u v : V} (h : G.Adj u v) {z : W},
      z ∈ (route h).support.tail → z ∈ Set.range f → z = f v)
    (hinteriorDisjoint : ∀ {a b c d : V} (h₁ : G.Adj a b) (h₂ : G.Adj c d),
      s(a,b) ≠ s(c,d) →
        List.Disjoint ((route h₁).support.tail.dropLast)
          ((route h₂).support.tail.dropLast))
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    List.Pairwise
      (fun d₁ d₂ => List.Disjoint ((route d₁.adj).support.tail)
        ((route d₂.adj).support.tail)) p.darts := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      have hpath := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
      rw [SimpleGraph.Walk.darts_cons, List.pairwise_cons]
      refine ⟨?_, ih hpath.1⟩
      intro d hd
      let d₀ : G.Dart := ⟨(u, v), h⟩
      have hd₀ : d₀ ∈ (SimpleGraph.Walk.cons h p).darts := by simp [d₀]
      have hdall : d ∈ (SimpleGraph.Walk.cons h p).darts := by
        simp [SimpleGraph.Walk.darts_cons, hd]
      have hedgesNe : s(u,v) ≠ s(d.fst,d.snd) := by
        intro he
        have hdeq := path_dart_edge_injective hp hd₀ hdall he
        have htarget : v = d.snd := by
          have heq' := congrArg (fun z : G.Dart => z.snd) hdeq
          simpa [d₀] using heq'
        exact (path_dart_snd_ne_start hpath.1 hd) htarget
      exact graphWalkRouteTails_disjoint_of_interiors G H f hf route
        hrouteRange hinteriorDisjoint h d.adj hedgesNe
        (path_dart_snd_ne_start hpath.1 hd)

/-- If the source map is injective, every replacement is a path, replacement
interiors avoid source-image vertices, and distinct source edges have disjoint
replacement interiors, then replacing all edges of a source path preserves
simplicity. The range condition says that a source-image vertex appearing in a
replacement suffix can only be its terminal endpoint. -/
theorem graphWalkSubstitute_isPath {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    (hroutePath : ∀ {u v : V} (h : G.Adj u v), (route h).IsPath)
    (hrouteRange : ∀ {u v : V} (h : G.Adj u v) {z : W},
      z ∈ (route h).support.tail → z ∈ Set.range f → z = f v)
    (hinteriorDisjoint : ∀ {a b c d : V} (h₁ : G.Adj a b) (h₂ : G.Adj c d),
      s(a,b) ≠ s(c,d) →
        List.Disjoint ((route h₁).support.tail.dropLast)
          ((route h₂).support.tail.dropLast))
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    (graphWalkSubstitute G H f route p).IsPath := by
  have hstart : f u ∉
      p.darts.flatMap fun d => (route d.adj).support.tail := by
    intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨d, hd, hz⟩
    have hrange : f u ∈ Set.range f := ⟨u, rfl⟩
    have heq := hrouteRange d.adj hz hrange
    have htarget := hf heq
    exact path_dart_snd_ne_start hp hd htarget
  have htailNodup :
      (p.darts.flatMap fun d => (route d.adj).support.tail).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨?_, graphWalkSubstitute_route_tails_pairwise G H f route hf
      hrouteRange hinteriorDisjoint p hp⟩
    intro d hd
    exact (hroutePath d.adj).support_nodup.tail
  rw [SimpleGraph.Walk.isPath_def]
  rw [← SimpleGraph.Walk.cons_tail_support
    (graphWalkSubstitute G H f route p)]
  rw [graphWalkSubstitute_support_tail]
  exact List.nodup_cons.mpr ⟨hstart, htailNodup⟩

private theorem graphWalkSubstitute_length_ge_source {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} (p : G.Walk u v) :
    p.length ≤ (graphWalkSubstitute G H f route p).length := by
  induction p with
  | nil => simp [graphWalkSubstitute]
  | @cons u v w h p ih =>
      rw [graphWalkSubstitute_cons, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons]
      have hpositive : 0 < (route h).length := by
        by_contra hnot
        have hzero : (route h).length = 0 := by omega
        have heq : f u = f v := SimpleGraph.Walk.eq_of_length_eq_zero hzero
        exact h.ne (hf heq)
      omega

/-- Under the same explicit route-intersection conditions as path substitution,
replacing the edges of an actual simple cycle preserves the cycle in the same
ordered walk. -/
theorem graphWalkSubstitute_isCycle {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    (hroutePath : ∀ {u v : V} (h : G.Adj u v), (route h).IsPath)
    (hrouteRange : ∀ {u v : V} (h : G.Adj u v) {z : W},
      z ∈ (route h).support.tail → z ∈ Set.range f → z = f v)
    (hinteriorDisjoint : ∀ {a b c d : V} (h₁ : G.Adj a b) (h₂ : G.Adj c d),
      s(a,b) ≠ s(c,d) →
        List.Disjoint ((route h₁).support.tail.dropLast)
          ((route h₂).support.tail.dropLast))
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    (graphWalkSubstitute G H f route p).IsCycle := by
  cases p with
  | nil => exact False.elim (hp.ne_nil rfl)
  | @cons u v _ h q =>
      have hcycle := (SimpleGraph.Walk.cons_isCycle_iff q h).mp hp
      have hqPath : q.IsPath := hcycle.1
      have hqSubPath := graphWalkSubstitute_isPath G H f hf route
        hroutePath hrouteRange hinteriorDisjoint q hqPath
      have hrouteDisjoint :
          List.Disjoint ((route h).support.tail)
            ((graphWalkSubstitute G H f route q).support.tail) := by
        rw [graphWalkSubstitute_support_tail]
        apply List.disjoint_left.mpr
        intro z hzRoute hzRest
        rcases List.mem_flatMap.mp hzRest with ⟨d, hd, hzD⟩
        have htargets : v ≠ d.snd := path_dart_snd_ne_start hqPath hd
        have hedgesNe : s(u,v) ≠ s(d.fst,d.snd) := by
          intro he
          have hedge : d.edge ∈ q.edges := List.mem_map.mpr ⟨d, hd, rfl⟩
          exact hcycle.2 (he ▸ hedge)
        exact (List.disjoint_left.mp
          (graphWalkRouteTails_disjoint_of_interiors G H f hf route
            hrouteRange hinteriorDisjoint h d.adj hedgesNe htargets)
          hzRoute) hzD
      have hqLength : 2 ≤ q.length := by
        have hlen := hp.three_le_length
        simp only [SimpleGraph.Walk.length_cons] at hlen
        omega
      have hsubLength := graphWalkSubstitute_length_ge_source G H f hf route q
      change ((route h).append (graphWalkSubstitute G H f route q)).IsCycle
      exact (hroutePath h).isCycle_append hqSubPath hrouteDisjoint
        (Or.inr (by omega))

end PottsContinuity.FKC.Medial
