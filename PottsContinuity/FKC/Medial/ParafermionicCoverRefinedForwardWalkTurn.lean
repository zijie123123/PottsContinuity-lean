-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedForwardWalkTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedForwardRouteTurn
public import PottsContinuity.FKC.Medial.GraphWalkPathSubstitution
public import PottsContinuity.FKC.Medial.ParafermionicCoverDirectedPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingSimplicity
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph PottsContinuity.FKC.FiniteFK

private theorem fin4_add_two_add_two (a : Fin 4) : (a + 2) + 2 = a := by
  fin_cases a <;> decide

private theorem compassLinearTurnSum_cons_cons (a b : Fin 4) (ds : List (Fin 4)) :
    parafermionicCoverCompassLinearTurnSum (a :: b :: ds) =
      primalCompassQuarterTurn a b +
        parafermionicCoverCompassLinearTurnSum (b :: ds) := by
  simp [parafermionicCoverCompassLinearTurnSum]

private theorem compassLinearTurnSum_singleton (a : Fin 4) :
    parafermionicCoverCompassLinearTurnSum [a] = 0 := by
  simp [parafermionicCoverCompassLinearTurnSum]

private theorem compassLinearTurnSum_boundary_append
    (pre : List (Fin 4)) (x y : Fin 4) (post : List (Fin 4)) :
    parafermionicCoverCompassLinearTurnSum (pre ++ [x] ++ y :: post) =
      parafermionicCoverCompassLinearTurnSum (pre ++ [x]) +
        parafermionicCoverCompassLinearTurnSum (y :: post) +
        primalCompassQuarterTurn x y := by
  induction pre with
  | nil =>
      simp [parafermionicCoverCompassLinearTurnSum]
      ring
  | cons a pre ih =>
      cases pre with
      | nil =>
          simp [parafermionicCoverCompassLinearTurnSum]
          ring
      | cons b pre =>
          have ih' :
              parafermionicCoverCompassLinearTurnSum
                  (b :: (pre ++ [x] ++ y :: post)) =
                parafermionicCoverCompassLinearTurnSum (b :: (pre ++ [x])) +
                  parafermionicCoverCompassLinearTurnSum (y :: post) +
                  primalCompassQuarterTurn x y := by
            simpa only [List.cons_append] using ih
          change parafermionicCoverCompassLinearTurnSum
              (a :: (b :: (pre ++ [x] ++ y :: post))) =
            parafermionicCoverCompassLinearTurnSum (a :: (b :: (pre ++ [x]))) +
              parafermionicCoverCompassLinearTurnSum (y :: post) +
              primalCompassQuarterTurn x y
          rw [compassLinearTurnSum_cons_cons a b (pre ++ [x] ++ y :: post),
            compassLinearTurnSum_cons_cons a b (pre ++ [x]), ih']
          ring

private theorem compassLinearTurnSum_remove_junction
    (pre : List (Fin 4)) (x y b : Fin 4) (post : List (Fin 4))
    (h : x = b ∨ y = b) :
    parafermionicCoverCompassLinearTurnSum (pre ++ [x] ++ y :: post) =
      parafermionicCoverCompassLinearTurnSum (pre ++ [x] ++ [b]) +
        parafermionicCoverCompassLinearTurnSum (b :: y :: post) := by
  rw [compassLinearTurnSum_boundary_append pre x y post,
    compassLinearTurnSum_boundary_append pre x b []]
  have hby := compassLinearTurnSum_cons_cons b y post
  rw [hby]
  have hself : primalCompassQuarterTurn b b = 0 := by
    fin_cases b <;> norm_num [primalCompassQuarterTurn]
  rw [compassLinearTurnSum_singleton]
  rcases h with rfl | rfl <;> rw [hself] <;> ring

private theorem compassLinearTurnSum_join_tangent
    (u b w : Fin 4) (ds es : List (Fin 4))
    (hds : ds ≠ []) (hes : es ≠ [])
    (hcontact : ds.getLast? = some b ∨ es.head? = some b) :
    parafermionicCoverCompassLinearTurnSum ([u] ++ ds ++ es ++ [w]) =
      parafermionicCoverCompassLinearTurnSum ([u] ++ ds ++ [b]) +
        parafermionicCoverCompassLinearTurnSum ([b] ++ es ++ [w]) := by
  let x := ds.getLast hds
  have hdecomp : ds.dropLast ++ [x] = ds := by
    exact List.dropLast_append_getLast hds
  rcases es with _ | ⟨y, tail⟩
  · simp at hes
  · have hxy : x = b ∨ y = b := by
      rcases hcontact with hl | hh
      · left
        have hget := List.getLast?_eq_getLast_of_ne_nil hds
        rw [hget] at hl
        exact Option.some.inj hl
      · right
        simpa using hh
    rw [← hdecomp]
    change parafermionicCoverCompassLinearTurnSum
          ((([u] ++ ds.dropLast) ++ [x]) ++ y :: tail ++ [w]) =
        parafermionicCoverCompassLinearTurnSum
          (([u] ++ ds.dropLast) ++ [x] ++ [b]) +
          parafermionicCoverCompassLinearTurnSum ([b] ++ y :: tail ++ [w])
    simpa [List.append_assoc] using
      compassLinearTurnSum_remove_junction ([u] ++ ds.dropLast) x y b
        (tail ++ [w]) hxy

private theorem refinedForwardRoute_starts_at_tangent_or_closed
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hf : parafermionicCoverFinitePairingForward n hn A u v) :
    (parafermionicCoverWalkCompassDirections
        (parafermionicCoverRefinedPairingRoute n hn A
          (parafermionicCoverFinitePairingForward_implies_adj n hn A hf))).head? =
        some (parafermionicCoverPortTangentCompass u.1.1) ∨
      (u.2 = false ∧ v.2 = false ∧
        parafermionicCoverPortBondState
          (parafermionicCoverConfigurationExtensionState n A) u.1.1 = false) := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv
  case false.false =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, hpair⟩
    by_cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1
    · left
      rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A
        hfRoute]
      simp [parafermionicCoverPortTangentCompass, hs, hleft]
    · exact Or.inr ⟨rfl, rfl, by simpa using hs⟩
  case false.true =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, heq⟩
    left
    rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A
      hfRoute]
    simp [parafermionicCoverPortTangentCompass, hleft]
  case true.false =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, heq⟩
    left
    rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A
      hfRoute]
    simp [parafermionicCoverPortTangentCompass, hleft]
  case true.true =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, hpair, hne⟩
    left
    rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A
      hfRoute]
    simp [parafermionicCoverPortTangentCompass, hleft]

private theorem refinedForwardRoute_ends_at_tangent_or_closed
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hf : parafermionicCoverFinitePairingForward n hn A u v) :
    (parafermionicCoverWalkCompassDirections
        (parafermionicCoverRefinedPairingRoute n hn A
          (parafermionicCoverFinitePairingForward_implies_adj n hn A hf))).getLast? =
        some (parafermionicCoverPortTangentCompass v.1.1) ∨
      (u.2 = false ∧ v.2 = false ∧
        parafermionicCoverPortBondState
          (parafermionicCoverConfigurationExtensionState n A) u.1.1 = false) := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv
  case false.false =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, hpair⟩
    by_cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1
    · have hraw : parafermionicCoverLocalPair
          (parafermionicCoverConfigurationExtensionState n A) u.1 = v.1 := by
        simpa only [parafermionicCoverFiniteLocalPairPerm_val] using
          congrArg Subtype.val hpair
      have hopen : parafermionicCoverOpenPair u.1 = v.1 := by
        simpa [parafermionicCoverLocalPair, hs] using hraw
      have hflagR : parafermionicCoverIncomingPrimalLeft v.1 = false := by
        rw [← hopen]
        simp [parafermionicCoverIncomingPrimalLeft_openPair, hleft]
      have hrad : parafermionicCoverPortRadialCompass v.1 + 2 =
          parafermionicCoverPortRadialCompass u.1 := by
        rw [← hopen, parafermionicCoverPortRadialCompass_openPair,
          fin4_add_two_add_two]
      left
      rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A
        hfRoute]
      simp [hs, parafermionicCoverPortTangentCompass, hflagR, hrad]
    · exact Or.inr ⟨rfl, rfl, by simpa using hs⟩
  case false.true =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, heq⟩
    have hright : parafermionicCoverIncomingPrimalLeft v.1 = false := by
      simpa [heq] using hleft
    left
    rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A
      hfRoute]
    simp [parafermionicCoverPortTangentCompass, hright, heq]
  case true.false =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, heq⟩
    have hright : parafermionicCoverIncomingPrimalLeft v.1 = true := by
      simpa [heq] using hleft
    left
    rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A
      hfRoute]
    simp [parafermionicCoverPortTangentCompass, hright, heq]
  case true.true =>
    have hfRoute := hf
    simp only [parafermionicCoverFinitePairingForward] at hf
    rcases hf with ⟨hleft, hpair, hne⟩
    have hcorner := parafermionicCoverRefinedPairingRoute_true_true_endpoint
      n hn A u v (parafermionicCoverFinitePairingForward_implies_adj n hn A hfRoute)
    have hflagR : parafermionicCoverIncomingPrimalLeft v.1 = true := by
      rw [hcorner]
      simp [parafermionicCoverIncomingPrimalLeft_cornerPair, hleft]
    left
    rw [parafermionicCoverRefinedForwardRoute_compassDirections n hn A hfRoute]
    simp [parafermionicCoverPortTangentCompass,
      parafermionicCoverIncomingPrimalLeft_cornerPair,
      parafermionicCoverPortRadialCompass_cornerPair, hleft, hcorner]

private theorem closedForwardStep_flips_target
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hf : parafermionicCoverFinitePairingForward n hn A u v)
    (hclosed : u.2 = false ∧ v.2 = false ∧
      parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1.1 = false) :
    parafermionicCoverIncomingPrimalLeft v.1.1 = false := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  rcases hclosed with ⟨rfl, rfl, hstate⟩
  simp only [parafermionicCoverFinitePairingForward] at hf
  rcases hf with ⟨hleft, hpair⟩
  have hraw : parafermionicCoverLocalPair
      (parafermionicCoverConfigurationExtensionState n A) u.1 = v.1 := by
    simpa only [parafermionicCoverFiniteLocalPairPerm_val] using
      congrArg Subtype.val hpair
  have hcap : parafermionicCoverClosedPair u.1 = v.1 := by
    simpa [parafermionicCoverLocalPair, hstate] using hraw
  rw [← hcap]
  simp [parafermionicCoverIncomingPrimalLeft_closedPair, hleft]

theorem parafermionicCoverRefinedForwardRoute_junction
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (h₁ : parafermionicCoverFinitePairingForward n hn A u v)
    (h₂ : parafermionicCoverFinitePairingForward n hn A v w) :
    (parafermionicCoverWalkCompassDirections
        (parafermionicCoverRefinedPairingRoute n hn A
          (parafermionicCoverFinitePairingForward_implies_adj n hn A h₁))).getLast? =
        some (parafermionicCoverPortTangentCompass v.1.1) ∨
      (parafermionicCoverWalkCompassDirections
        (parafermionicCoverRefinedPairingRoute n hn A
          (parafermionicCoverFinitePairingForward_implies_adj n hn A h₂))).head? =
        some (parafermionicCoverPortTangentCompass v.1.1) := by
  have hend := refinedForwardRoute_ends_at_tangent_or_closed n hn A h₁
  rcases hend with hend | hclosed
  · exact Or.inl hend
  have hstart := refinedForwardRoute_starts_at_tangent_or_closed n hn A h₂
  rcases hstart with hstart | hclosed'
  · exact Or.inr hstart
  have hflip := closedForwardStep_flips_target n hn A h₁ hclosed
  have hleft : parafermionicCoverIncomingPrimalLeft v.1.1 = true := by
    rcases hclosed' with ⟨hv, hw, _⟩
    have h₂' := h₂
    simp only [parafermionicCoverFinitePairingForward, hv, hw] at h₂'
    exact h₂'.1
  rw [hflip] at hleft
  cases hleft

private theorem refinedForwardRoute_compassDirections_ne_nil
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hf : parafermionicCoverFinitePairingForward n hn A u v) :
    parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedPairingRoute n hn A
        (parafermionicCoverFinitePairingForward_implies_adj n hn A hf)) ≠ [] := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  have hdirs := parafermionicCoverRefinedForwardRoute_compassDirections n hn A hf
  cases bu <;> cases bv
  all_goals simp only at hdirs
  all_goals rw [hdirs]
  all_goals
    by_cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1
    <;> simp [hs]

theorem parafermionicCoverRefinedForwardWalkTurn_identity
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (hforward : ∀ d ∈ p.darts,
      parafermionicCoverFinitePairingForward n hn A d.fst d.snd) :
    parafermionicCoverCompassLinearTurnSum
        ([parafermionicCoverPortTangentCompass u.1.1] ++
          parafermionicCoverWalkCompassDirections
            (parafermionicCoverRefinedPairingWalk n hn A p) ++
          [parafermionicCoverPortTangentCompass v.1.1]) =
      parafermionicCoverFinitePairingWalkTurn n hn A p +
        parafermionicCoverPortTangentPhase v.1.1 -
          parafermionicCoverPortTangentPhase u.1.1 := by
  revert hforward
  induction p with
  | nil =>
      intro _
      simp [parafermionicCoverRefinedPairingWalk,
        parafermionicCoverCompassLinearTurnSum,
        parafermionicCoverFinitePairingWalkTurn,
        parafermionicCoverPortTangentCompass,
        parafermionicCoverPortTangentPhase,
        primalCompassQuarterTurn]
  | @cons a b c h tail ih =>
      intro hforward
      have hcur : parafermionicCoverFinitePairingForward n hn A a b := by
        exact hforward ⟨(a, b), h⟩ (by simp [Walk.darts_cons])
      have htail : ∀ d ∈ tail.darts,
          parafermionicCoverFinitePairingForward n hn A d.fst d.snd := by
        intro d hd
        apply hforward d
        simp [Walk.darts_cons, hd]
      have hadj := parafermionicCoverFinitePairingForward_implies_adj n hn A hcur
      have hproof : h = hadj := Subsingleton.elim _ _
      have hrouteEq : parafermionicCoverRefinedPairingRoute n hn A h =
          parafermionicCoverRefinedPairingRoute n hn A hadj := by
        exact congrArg (parafermionicCoverRefinedPairingRoute n hn A) hproof
      have hrouteDirs := parafermionicCoverRefinedForwardRoute_compassDirections
        n hn A hcur
      have hlocal := parafermionicCoverRefinedForwardRouteTurn_identity n hn A hcur
      cases tail with
      | nil =>
          simp only [parafermionicCoverRefinedPairingWalk,
            graphWalkSubstitute_cons, graphWalkSubstitute_nil,
            parafermionicCoverWalkCompassDirections_append,
            parafermionicCoverWalkCompassDirections_nil,
            parafermionicCoverFinitePairingWalkTurn, Walk.darts_cons,
            List.map_cons, List.sum_cons]
          rw [hrouteEq]
          rw [hrouteDirs]
          rw [hrouteDirs] at hlocal
          simpa using hlocal
      | @cons b z d h₂ rest =>
          have h₂forward : parafermionicCoverFinitePairingForward n hn A b z := by
            apply hforward ⟨(b, z), h₂⟩
            simp [Walk.darts_cons]
          have hrest : ∀ e ∈ rest.darts,
              parafermionicCoverFinitePairingForward n hn A e.fst e.snd := by
            intro e he
            apply hforward e
            simp [Walk.darts_cons, he]
          have hadj₂ := parafermionicCoverFinitePairingForward_implies_adj n hn A h₂forward
          have hrouteEq₂ : parafermionicCoverRefinedPairingRoute n hn A h₂ =
              parafermionicCoverRefinedPairingRoute n hn A hadj₂ := by
            exact congrArg (parafermionicCoverRefinedPairingRoute n hn A)
              (Subsingleton.elim _ _)
          let d₁ := parafermionicCoverWalkCompassDirections
            (parafermionicCoverRefinedPairingRoute n hn A hadj)
          let d₂ := parafermionicCoverWalkCompassDirections
            (parafermionicCoverRefinedPairingRoute n hn A hadj₂)
          let dtail := parafermionicCoverWalkCompassDirections
            (parafermionicCoverRefinedPairingWalk n hn A (Walk.cons h₂ rest))
          let drest := parafermionicCoverWalkCompassDirections
            (parafermionicCoverRefinedPairingWalk n hn A rest)
          have hcomp₂ : dtail = d₂ ++ drest := by
            simp [dtail, d₂, drest, parafermionicCoverRefinedPairingWalk,
              graphWalkSubstitute_cons, parafermionicCoverWalkCompassDirections_append,
              hrouteEq₂]
          have hnonempty₁ : d₁ ≠ [] := by
            exact refinedForwardRoute_compassDirections_ne_nil n hn A hcur
          have hnonempty₂ : d₂ ≠ [] := by
            exact refinedForwardRoute_compassDirections_ne_nil n hn A h₂forward
          have hjunction := parafermionicCoverRefinedForwardRoute_junction
            n hn A hcur h₂forward
          have hcontact : d₁.getLast? = some (parafermionicCoverPortTangentCompass b.1.1) ∨
              dtail.head? = some (parafermionicCoverPortTangentCompass b.1.1) := by
            rcases hjunction with hlast | hhead
            · left
              simpa [d₁, hadj] using hlast
            · right
              have hhead₂ : d₂.head? = some (parafermionicCoverPortTangentCompass b.1.1) := by
                simpa [d₂, hadj₂] using hhead
              rw [hcomp₂]
              simp [List.head?_append, hhead₂]
          have hjoin := compassLinearTurnSum_join_tangent
            (parafermionicCoverPortTangentCompass a.1.1)
            (parafermionicCoverPortTangentCompass b.1.1)
            (parafermionicCoverPortTangentCompass c.1.1)
            d₁ dtail hnonempty₁ (by
              rw [hcomp₂]
              intro hnil
              have hnil' : d₂ = [] ∧ drest = [] := List.append_eq_nil_iff.mp hnil
              exact hnonempty₂ hnil'.1) hcontact
          have hlocal' :
              parafermionicCoverCompassLinearTurnSum
                  ([parafermionicCoverPortTangentCompass a.1.1] ++ d₁ ++
                    [parafermionicCoverPortTangentCompass b.1.1]) =
                parafermionicCoverFinitePairingStepTurn n A a b +
                  parafermionicCoverPortTangentPhase b.1.1 -
                    parafermionicCoverPortTangentPhase a.1.1 := by
            simpa [d₁, hadj] using hlocal
          have ih' := ih htail
          have hcompP :
              parafermionicCoverWalkCompassDirections
                  (parafermionicCoverRefinedPairingWalk n hn A
                    (Walk.cons h (Walk.cons h₂ rest))) = d₁ ++ dtail := by
            simp [d₁, dtail, parafermionicCoverRefinedPairingWalk,
              graphWalkSubstitute_cons, parafermionicCoverWalkCompassDirections_append,
              hrouteEq]
          have hturn : parafermionicCoverFinitePairingWalkTurn n hn A
                (Walk.cons h (Walk.cons h₂ rest)) =
              parafermionicCoverFinitePairingStepTurn n A a b +
                parafermionicCoverFinitePairingWalkTurn n hn A
                  (Walk.cons h₂ rest) := by
            simp [parafermionicCoverFinitePairingWalkTurn, Walk.darts_cons,
              List.map_cons, List.sum_cons]
          have hjoin' :
              parafermionicCoverCompassLinearTurnSum
                  ([parafermionicCoverPortTangentCompass a.1.1] ++
                    (d₁ ++ dtail) ++ [parafermionicCoverPortTangentCompass c.1.1]) =
                parafermionicCoverCompassLinearTurnSum
                    ([parafermionicCoverPortTangentCompass a.1.1] ++ d₁ ++
                      [parafermionicCoverPortTangentCompass b.1.1]) +
                  parafermionicCoverCompassLinearTurnSum
                    ([parafermionicCoverPortTangentCompass b.1.1] ++ dtail ++
                      [parafermionicCoverPortTangentCompass c.1.1]) := by
            simpa [List.append_assoc] using hjoin
          rw [hcompP, hjoin', hlocal', ih', hturn]
          ring

end PottsContinuity.FKC.Medial
