-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedSourceCycle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingSimplicity
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerInterior
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationSupport
public import PottsContinuity.FKC.Medial.ParafermionicCoverOriginCorner
public import PottsContinuity.FKC.Medial.PairingSingleCut
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph
open PottsContinuity.FKC.FiniteFK

noncomputable abbrev refinedOriginSourcePath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :=
  parafermionicCoverFiniteOriginExplorationPath n hn A

noncomputable abbrev refinedOriginSourceWalk (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :=
  parafermionicCoverRefinedPairingWalk n hn A (refinedOriginSourcePath n hn A)

private theorem refinedOriginSourceWalk_isPath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (refinedOriginSourceWalk n hn A).IsPath :=
  parafermionicCoverRefinedPairingWalk_isPath n hn A _
    (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A)

private theorem graphWalkSubstitute_support_tail {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} (p : G.Walk u v) :
    (graphWalkSubstitute G H f route p).support.tail =
      p.darts.flatMap fun d => (route d.adj).support.tail := by
  induction p with
  | nil => simp [graphWalkSubstitute]
  | cons h p ih =>
      rw [graphWalkSubstitute_cons, Walk.tail_support_append, Walk.darts_cons,
        List.flatMap_cons, ih]

private theorem refinedOriginSourceWalk_tail_flatMap (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (refinedOriginSourceWalk n hn A).support.tail =
      (refinedOriginSourcePath n hn A).darts.flatMap fun d =>
        (parafermionicCoverRefinedPairingRoute n hn A d.adj).support.tail := by
  simpa [refinedOriginSourceWalk, refinedOriginSourcePath,
    parafermionicCoverRefinedPairingWalk] using
    (graphWalkSubstitute_support_tail
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
      parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
      (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h)
      (parafermionicCoverFiniteOriginExplorationPath n hn A))

private theorem refinedRoute_tail_getLast (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    ∃ hne : (parafermionicCoverRefinedPairingRoute n hn A h).support.tail ≠ [],
      (parafermionicCoverRefinedPairingRoute n hn A h).support.tail.getLast hne =
        parafermionicCoverRefinedPairingEmbedding v := by
  have hpositive : 0 < (parafermionicCoverRefinedPairingRoute n hn A h).length := by
    by_contra hnot
    have hzero : (parafermionicCoverRefinedPairingRoute n hn A h).length = 0 := by omega
    have heq : parafermionicCoverRefinedPairingEmbedding u =
        parafermionicCoverRefinedPairingEmbedding v := Walk.eq_of_length_eq_zero hzero
    exact h.ne (parafermionicCoverRefinedPairingEmbedding_injective n heq)
  have htailLength : (parafermionicCoverRefinedPairingRoute n hn A h).support.tail.length =
      (parafermionicCoverRefinedPairingRoute n hn A h).length := by
    rw [List.length_tail, Walk.length_support]
    omega
  have hne : (parafermionicCoverRefinedPairingRoute n hn A h).support.tail ≠ [] := by
    intro hnil
    have hlen : (parafermionicCoverRefinedPairingRoute n hn A h).support.tail.length = 0 := by
      simp [hnil]
    rw [htailLength] at hlen
    omega
  refine ⟨hne, ?_⟩
  simp

private theorem refinedRouteInteriorClassification (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (parafermionicCoverRefinedPairingRoute n hn A h).support.tail.dropLast) :
    (u.2 = false ∧ v.2 = false ∧
      parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1.1 = false ∧
      v.1.1 = parafermionicCoverClosedPair u.1.1 ∧
      z = parafermionicCoverRefinedClosedCapMiddle u.1.1) ∨
    (u.2 = true ∧ v.2 = true ∧
      v.1.1 = parafermionicCoverCornerPair u.1.1 ∧
      z ∈ parafermionicCoverRefinedCornerWalkInterior u.1.1) := by
  rcases u with ⟨c, bc⟩
  rcases v with ⟨d, bd⟩
  have hshape := parafermionicCoverRefinedPairingRoute_interior n hn A h
  rw [hshape] at hz
  cases bc <;> cases bd
  · rcases parafermionicCoverRefinedPairingRoute_false_false_endpoint n hn A c d h with
      ⟨hs, hopen⟩ | ⟨hs, hclosed⟩
    · simp [hs] at hz
    · have hzmid : z = parafermionicCoverRefinedClosedCapMiddle c.1 := by
        simpa [hs] using hz
      exact Or.inl ⟨rfl, rfl, hs, hclosed, hzmid⟩
  · simp at hz
  · simp at hz
  · have hcorner := parafermionicCoverRefinedPairingRoute_true_true_endpoint n hn A c d h
    have hzlist : z ∈ [parafermionicCoverRefinedCornerMid₁ c.1,
        parafermionicCoverRefinedCornerElbow c.1,
        parafermionicCoverRefinedCornerMid₂ c.1] := by
      simpa using hz
    have hzcorner : z ∈ parafermionicCoverRefinedCornerWalkInterior c.1 :=
      (parafermionicCoverRefinedCornerWalkInterior_eq c.1).symm ▸ hzlist
    exact Or.inr ⟨rfl, rfl, hcorner, hzcorner⟩

private theorem no_source_edge_has_origin_corner_interior (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (parafermionicCoverRefinedPairingRoute n hn A h).support.tail.dropLast)
    (hzCorner : z ∈ parafermionicCoverRefinedCornerWalkInterior
      parafermionicCoverOriginCornerPortOther) : False := by
  rcases refinedRouteInteriorClassification n hn A h hz with
    ⟨hu, hv, hstate, hpair, hcap⟩ | ⟨hu, hv, hpair, hrouteCorner⟩
  · exact (parafermionicCoverRefinedCornerInterior_ne_closedCapMiddle
      parafermionicCoverOriginCornerPortOther u.1.1 hzCorner) hcap
  · have hclass := parafermionicCoverRefinedCornerInterior_eq_classification
      u.1.1 parafermionicCoverOriginCornerPortOther hrouteCorner hzCorner rfl
    have hcutPort : u.1 = parafermionicCoverFiniteOriginCornerPort n hn ∨
        u.1 = parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn) := by
      rcases hclass with hsame | hrev
      · right
        apply Subtype.ext
        calc
          u.1.1 = parafermionicCoverOriginCornerPortOther := hsame.symm
          _ = (parafermionicCoverFiniteCornerPairPerm n
              (parafermionicCoverFiniteOriginCornerPort n hn)).1 := by
            symm
            exact parafermionicCoverFiniteCornerPairPerm_origin n hn
      · left
        apply Subtype.ext
        have hother : parafermionicCoverCornerPair
            parafermionicCoverOriginCornerPortOther = parafermionicCoverOriginCornerPort := by
          rw [parafermionicCoverOriginCornerPortOther]
          exact parafermionicCoverCornerPair_involutive _
        calc
          u.1.1 = parafermionicCoverCornerPair
              parafermionicCoverOriginCornerPortOther := by
                have hcp : parafermionicCoverCornerPair
                    parafermionicCoverOriginCornerPortOther = u.1.1 := by
                  calc
                    parafermionicCoverCornerPair
                        parafermionicCoverOriginCornerPortOther =
                      parafermionicCoverCornerPair
                        (parafermionicCoverCornerPair u.1.1) :=
                      congrArg parafermionicCoverCornerPair hrev
                    _ = u.1.1 := parafermionicCoverCornerPair_involutive _
                exact hcp.symm
          _ = parafermionicCoverOriginCornerPort := hother
    let C := parafermionicCoverFiniteCornerPairPerm n
    let s := parafermionicCoverFiniteOriginCornerPort n hn
    have hfix : pairingSingleCutPerm C s
        (parafermionicCoverFiniteCornerPairPerm_involutive n) u.1 = u.1 := by
      apply (pairingSingleCutPerm_fixed_iff C s u.1
        (parafermionicCoverFiniteCornerPairPerm_involutive n)
        (parafermionicCoverFiniteCornerPairPerm_no_fixed_points n)).2
      rcases hcutPort with hs | hs
      · exact Or.inl hs
      · exact Or.inr hs
    have hadj' := (parafermionicCoverFiniteCornerCutPairingGraph_adj_iff n hn A u v).mp h
    simp [hu, hv] at hadj'
    rcases hadj' with ⟨hpairCut, hne⟩
    exact hne (hfix.symm.trans hpairCut)

private theorem refinedOriginCornerInterior_not_in_sourceTail (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    List.Disjoint (refinedOriginSourceWalk n hn A).support.tail
      (parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther).support.tail := by
  have hqpath := refinedOriginSourceWalk_isPath n hn A
  have hstartNot : parafermionicCoverRefinedPairingEmbedding
      (parafermionicCoverFiniteOriginCornerPort n hn, true) ∉
      (refinedOriginSourceWalk n hn A).support.tail := by
    have hnodup := hqpath.support_nodup
    rw [← Walk.cons_tail_support (refinedOriginSourceWalk n hn A)] at hnodup
    simpa [refinedOriginSourceWalk, parafermionicCoverRefinedPairingWalk,
      parafermionicCoverRefinedPairingEmbedding] using (List.nodup_cons.mp hnodup).1
  have hstart : parafermionicCoverRefinedPairingEmbedding
      (parafermionicCoverFiniteOriginCornerPort n hn, true) =
      parafermionicCoverRefinedPortEmbedding
        (parafermionicCoverOriginCornerPort, true) := by
    simp [parafermionicCoverRefinedPairingEmbedding,
      parafermionicCoverFiniteOriginCornerPort_val]
  have htail :
      (parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther).support.tail =
        [parafermionicCoverRefinedCornerMid₁ parafermionicCoverOriginCornerPortOther,
         parafermionicCoverRefinedCornerElbow parafermionicCoverOriginCornerPortOther,
         parafermionicCoverRefinedCornerMid₂ parafermionicCoverOriginCornerPortOther,
         parafermionicCoverRefinedPortEmbedding
           (parafermionicCoverOriginCornerPort, true)] := by
    rw [parafermionicCoverRefinedCornerWalk_support]
    simp only [List.tail_cons, parafermionicCoverOriginCornerPortOther]
    rw [parafermionicCoverCornerPair_involutive]
  apply List.disjoint_left.mpr
  intro z hzq hzc
  rw [htail] at hzc
  simp only [List.mem_cons, List.not_mem_nil] at hzc
  rcases hzc with hmid₁ | hmid₂ | hmid₃ | horigin
  · subst z
    have hzcorner : parafermionicCoverRefinedCornerMid₁
        parafermionicCoverOriginCornerPortOther ∈
        parafermionicCoverRefinedCornerWalkInterior
          parafermionicCoverOriginCornerPortOther := by
      rw [parafermionicCoverRefinedCornerWalkInterior_eq]
      simp
    rw [refinedOriginSourceWalk_tail_flatMap n hn A] at hzq
    rcases List.mem_flatMap.mp hzq with ⟨d, hd, hzroute⟩
    obtain ⟨hne, hlast⟩ := refinedRoute_tail_getLast n hn A d.adj
    by_cases hzlast : parafermionicCoverRefinedCornerMid₁
        parafermionicCoverOriginCornerPortOther =
          (parafermionicCoverRefinedPairingRoute n hn A d.adj).support.tail.getLast hne
    · have hnot := parafermionicCoverRefinedCornerInterior_ne_portEmbedding
        parafermionicCoverOriginCornerPortOther d.snd.1 d.snd.2 hzcorner
      exact hnot (hzlast.trans hlast)
    · have hzinterior := List.mem_dropLast_of_mem_of_ne_getLast hzroute hzlast
      exact no_source_edge_has_origin_corner_interior n hn A d.adj hzinterior hzcorner
  · subst z
    have hzcorner : parafermionicCoverRefinedCornerElbow
        parafermionicCoverOriginCornerPortOther ∈
        parafermionicCoverRefinedCornerWalkInterior
          parafermionicCoverOriginCornerPortOther := by
      rw [parafermionicCoverRefinedCornerWalkInterior_eq]
      simp
    rw [refinedOriginSourceWalk_tail_flatMap n hn A] at hzq
    rcases List.mem_flatMap.mp hzq with ⟨d, hd, hzroute⟩
    obtain ⟨hne, hlast⟩ := refinedRoute_tail_getLast n hn A d.adj
    by_cases hzlast : parafermionicCoverRefinedCornerElbow
        parafermionicCoverOriginCornerPortOther =
          (parafermionicCoverRefinedPairingRoute n hn A d.adj).support.tail.getLast hne
    · have hnot := parafermionicCoverRefinedCornerInterior_ne_portEmbedding
        parafermionicCoverOriginCornerPortOther d.snd.1 d.snd.2 hzcorner
      exact hnot (hzlast.trans hlast)
    · have hzinterior := List.mem_dropLast_of_mem_of_ne_getLast hzroute hzlast
      exact no_source_edge_has_origin_corner_interior n hn A d.adj hzinterior hzcorner
  · subst z
    have hzcorner : parafermionicCoverRefinedCornerMid₂
        parafermionicCoverOriginCornerPortOther ∈
        parafermionicCoverRefinedCornerWalkInterior
          parafermionicCoverOriginCornerPortOther := by
      rw [parafermionicCoverRefinedCornerWalkInterior_eq]
      simp
    rw [refinedOriginSourceWalk_tail_flatMap n hn A] at hzq
    rcases List.mem_flatMap.mp hzq with ⟨d, hd, hzroute⟩
    obtain ⟨hne, hlast⟩ := refinedRoute_tail_getLast n hn A d.adj
    by_cases hzlast : parafermionicCoverRefinedCornerMid₂
        parafermionicCoverOriginCornerPortOther =
          (parafermionicCoverRefinedPairingRoute n hn A d.adj).support.tail.getLast hne
    · have hnot := parafermionicCoverRefinedCornerInterior_ne_portEmbedding
        parafermionicCoverOriginCornerPortOther d.snd.1 d.snd.2 hzcorner
      exact hnot (hzlast.trans hlast)
    · have hzinterior := List.mem_dropLast_of_mem_of_ne_getLast hzroute hzlast
      exact no_source_edge_has_origin_corner_interior n hn A d.adj hzinterior hzcorner
  · rcases horigin with horigin | hfalse
    · have horigin' : z = parafermionicCoverRefinedPairingEmbedding
        (parafermionicCoverFiniteOriginCornerPort n hn, true) := by
          calc
            z = parafermionicCoverRefinedPortEmbedding
                (parafermionicCoverOriginCornerPort, true) := horigin
            _ = parafermionicCoverRefinedPairingEmbedding
                (parafermionicCoverFiniteOriginCornerPort n hn, true) := hstart.symm
      exact hstartNot (horigin' ▸ hzq)
    · exact hfalse

 theorem refinedSourceCorner_start_eq (n : ℕ) (hn : 1 ≤ n)
    (_A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverRefinedPortEmbedding
        (parafermionicCoverOriginCornerPortOther, true) =
      parafermionicCoverRefinedPairingEmbedding
        (parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn), true) := by
  change parafermionicCoverRefinedPortEmbedding
      (parafermionicCoverOriginCornerPortOther, true) =
    parafermionicCoverRefinedPortEmbedding
      (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort, true)
  rfl

 theorem refinedSourceCorner_end_eq (n : ℕ) (hn : 1 ≤ n)
    (_A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverRefinedPortEmbedding
        (parafermionicCoverCornerPair parafermionicCoverOriginCornerPortOther, true) =
      parafermionicCoverRefinedPairingEmbedding
        (parafermionicCoverFiniteOriginCornerPort n hn, true) := by
  apply congrArg (fun c : ParafermionicCoverPort =>
    parafermionicCoverRefinedPortEmbedding (c, true))
  rw [parafermionicCoverOriginCornerPortOther]
  exact parafermionicCoverCornerPair_involutive _

/-- The actual refined source cycle: substitute every edge of the chosen actual
origin exploration path and close it by the named actual corner route from the
other origin port back to the origin port. -/
noncomputable def parafermionicCoverRefinedSourceCycle (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverGraph.Walk
      (parafermionicCoverRefinedPairingEmbedding
        (parafermionicCoverFiniteOriginCornerPort n hn, true))
      (parafermionicCoverRefinedPairingEmbedding
        (parafermionicCoverFiniteOriginCornerPort n hn, true)) := by
  let q := refinedOriginSourceWalk n hn A
  let c := parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther
  have hc := c.copy (refinedSourceCorner_start_eq n hn A)
      (refinedSourceCorner_end_eq n hn A)
  exact q.append hc

theorem parafermionicCoverRefinedSourceCycle_isCycle (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (parafermionicCoverRefinedSourceCycle n hn A).IsCycle := by
  let q := refinedOriginSourceWalk n hn A
  let c := parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther
  have hq : q.IsPath := refinedOriginSourceWalk_isPath n hn A
  have hc : c.IsPath := parafermionicCoverRefinedCornerWalk_isPath _
  have hdisj : List.Disjoint q.support.tail c.support.tail := by
    simpa [q, c, Walk.support_copy] using
      refinedOriginCornerInterior_not_in_sourceTail n hn A
  have hcycle : (q.append (c.copy (refinedSourceCorner_start_eq n hn A)
      (refinedSourceCorner_end_eq n hn A))).IsCycle := by
    apply hq.isCycle_append
    · exact hc
    · exact hdisj
    · exact Or.inr (by
        rw [Walk.length_copy, parafermionicCoverRefinedCornerWalk_length]
        norm_num)
  simpa [parafermionicCoverRefinedSourceCycle, q, c] using hcycle

end PottsContinuity.FKC.Medial
