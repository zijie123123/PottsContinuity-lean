-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutPartner.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutTerminals
public import PottsContinuity.FKC.FiniteFK.CriticalEdgeToggle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance edgeCutPartnerPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance edgeCutPartnerGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

/-- The six actual degree-one terminals, expressed without reference to the configuration. -/
def parafermionicCoverFiniteEdgeCutTerminals (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) : Finset (ParafermionicCoverFinitePort n × Bool) :=
  (parafermionicCoverFiniteEdgeCutQueriedPorts n e).image (fun c => (c, false)) ∪
    parafermionicCoverFiniteEdgeCutCornerTerminals n hn

theorem parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutTerminals n hn e =
      parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
  symm
  exact parafermionicCoverFiniteEdgeCutDegreeOne_carrier n hn A e

theorem parafermionicCoverFiniteEdgeCutTerminals_card (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutTerminals n hn e).card = 6 := by
  classical
  rw [parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn
    (∅ : Configuration (ParafermionicAmbientGraph n)) e]
  exact parafermionicCoverFiniteEdgeCutDegreeOneVertices_card n hn _ e

abbrev ParafermionicCoverFiniteEdgeCutTerminal (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :=
  {v : ParafermionicCoverFinitePort n × Bool //
    v ∈ parafermionicCoverFiniteEdgeCutTerminals n hn e}

local instance terminalFintype (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype (ParafermionicCoverFiniteEdgeCutTerminal n hn e) :=
  by classical exact Fintype.ofFinite _

 theorem edgeCutPartner_existsUnique (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (s : ParafermionicCoverFiniteEdgeCutTerminal n hn e) :
    ∃! t : ParafermionicCoverFiniteEdgeCutTerminal n hn e,
      t.1 ≠ s.1 ∧
        (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable s.1 t.1 := by
  classical
  have hsdegree : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree s.1 = 1 := by
    have hmem : s.val ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
      rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
      exact s.property
    exact (Finset.mem_filter.mp hmem).2
  obtain ⟨t, ⟨hts, htdeg, hreach⟩, huniq⟩ :=
    parafermionicCoverFiniteEdgeCutGraph_existsUnique_partner
      n hn A e s.val hsdegree
  have htmem : t ∈ parafermionicCoverFiniteEdgeCutTerminals n hn e := by
    rw [parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htdeg⟩
  refine ⟨⟨t, htmem⟩, ⟨hts, hreach⟩, ?_⟩
  intro u hu
  apply Subtype.ext
  apply huniq u.val
  · rcases hu with ⟨hne, hreach⟩
    have hdeg : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree u.val = 1 := by
      have hmem : u.val ∈ parafermionicCoverFiniteEdgeCutTerminals n hn e := u.property
      simp only [parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e] at hmem
      exact (Finset.mem_filter.mp hmem).2
    exact ⟨hne, hdeg, hreach⟩

def parafermionicCoverFiniteEdgeCutPartner (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (s : ParafermionicCoverFiniteEdgeCutTerminal n hn e) :
    ParafermionicCoverFiniteEdgeCutTerminal n hn e :=
  Classical.choose (edgeCutPartner_existsUnique n hn A e s)

theorem parafermionicCoverFiniteEdgeCutPartner_spec (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (s : ParafermionicCoverFiniteEdgeCutTerminal n hn e) :
    parafermionicCoverFiniteEdgeCutPartner n hn A e s ≠ s ∧
      (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable s.1
        (parafermionicCoverFiniteEdgeCutPartner n hn A e s).1 := by
  rcases (Classical.choose_spec (edgeCutPartner_existsUnique n hn A e s)).1 with
    ⟨hne, hreach⟩
  exact ⟨fun h => hne (congrArg Subtype.val h), hreach⟩

theorem parafermionicCoverFiniteEdgeCutPartner_involutive (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Function.Involutive (parafermionicCoverFiniteEdgeCutPartner n hn A e) := by
  intro s
  have hst := parafermionicCoverFiniteEdgeCutPartner_spec n hn A e s
  have hts := parafermionicCoverFiniteEdgeCutPartner_spec n hn A e
    (parafermionicCoverFiniteEdgeCutPartner n hn A e s)
  apply Subtype.ext
  have huniq := (Classical.choose_spec
    (edgeCutPartner_existsUnique n hn A e
      (parafermionicCoverFiniteEdgeCutPartner n hn A e s))).2
  have hsprop : s.1 ≠ (parafermionicCoverFiniteEdgeCutPartner n hn A e s).1 ∧
      (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable
        (parafermionicCoverFiniteEdgeCutPartner n hn A e s).1 s.1 :=
    ⟨fun h => hst.1 (Subtype.ext h.symm), hst.2.symm⟩
  exact (congrArg Subtype.val (huniq s hsprop)).symm

theorem parafermionicCoverFiniteEdgeCutPartner_toggle_eq (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (s : ParafermionicCoverFiniteEdgeCutTerminal n hn e) :
    parafermionicCoverFiniteEdgeCutPartner n hn A e s =
      parafermionicCoverFiniteEdgeCutPartner n hn (toggleEdgeConfiguration e A) e s := by
  apply Subtype.ext
  have hgraph := parafermionicCoverFiniteEdgeCutGraph_toggle_eq n hn A e
  have hspec := parafermionicCoverFiniteEdgeCutPartner_spec n hn A e s
  have hspec' := parafermionicCoverFiniteEdgeCutPartner_spec n hn
    (toggleEdgeConfiguration e A) e s
  have huniq := (Classical.choose_spec (edgeCutPartner_existsUnique n hn A e s)).2
  have hreach : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable s.1
      (parafermionicCoverFiniteEdgeCutPartner n hn (toggleEdgeConfiguration e A) e s).1 := by
    simpa only [hgraph] using hspec'.2
  have hne : (parafermionicCoverFiniteEdgeCutPartner n hn
      (toggleEdgeConfiguration e A) e s).val ≠ s.val := by
    intro h
    exact hspec'.1 (Subtype.ext h)
  exact (congrArg Subtype.val (huniq (parafermionicCoverFiniteEdgeCutPartner n hn
    (toggleEdgeConfiguration e A) e s) ⟨hne, hreach⟩)).symm

end
end PottsContinuity.FKC.FiniteFK
