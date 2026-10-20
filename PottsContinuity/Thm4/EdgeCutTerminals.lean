/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutTerminals.lean`.
Adaptation: namespace relocation and existing exact edge-port carrier.
-/
module

public import PottsContinuity.Thm4.EdgeCutGraph
public import PottsContinuity.Thm4.EdgePorts
public import PottsContinuity.Thm4.TerminalPairing
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
open SimpleGraph
noncomputable section

local instance edgeCutTerminalPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance edgeCutTerminalGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

/-- The retained false-layer port occurrences which query the selected actual edge. -/
def parafermionicCoverFiniteEdgeCutQueriedPorts (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) : Finset (ParafermionicCoverFinitePort n) :=
  Finset.univ.filter fun c =>
    parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e

/-- Degree-one vertices of the actual edge-cut pairing graph. -/
def parafermionicCoverFiniteEdgeCutDegreeOneVertices (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Finset (ParafermionicCoverFinitePort n × Bool) :=
  Finset.univ.filter fun v =>
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree v = 1

/-- The two true-layer corner terminals of the original corner cut. -/
def parafermionicCoverFiniteEdgeCutCornerTerminals (n : ℕ) (hn : 1 ≤ n) :
    Finset (ParafermionicCoverFinitePort n × Bool) :=
  {(parafermionicCoverFiniteOriginCornerPort n hn, true),
    (parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn), true)}

theorem parafermionicCoverFiniteEdgeCutDegreeOne_true_iff (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree (c, true) = 1 ↔
      c = parafermionicCoverFiniteOriginCornerPort n hn ∨
        c = parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn) := by
  let C := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  have hC : Function.Involutive C := parafermionicCoverFiniteCornerPairPerm_involutive n
  have hCfree : ∀ p, C p ≠ p := parafermionicCoverFiniteCornerPairPerm_no_fixed_points n
  have hfixed : pairingSingleCutPerm C s hC c = c ↔ c = s ∨ c = C s := by
    exact pairingSingleCutPerm_fixed_iff C s c hC hCfree
  constructor
  · intro hdeg
    by_cases hf : pairingSingleCutPerm C s hC c = c
    · exact hfixed.mp hf
    · have htwo := parafermionicCoverFiniteEdgeCutGraph_degree_true_of_not_fixed n hn A e c hf
      rw [htwo] at hdeg
      omega
  · intro hterm
    apply parafermionicCoverFiniteEdgeCutGraph_degree_true_of_fixed n hn A e c
    exact hfixed.mpr hterm

theorem parafermionicCoverFiniteEdgeCutQueriedFalse_mem_iff (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n) :
    (c, false) ∈
        (parafermionicCoverFiniteEdgeCutQueriedPorts n e).image (fun d => (d, false)) ↔
      parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
  classical
  simp only [parafermionicCoverFiniteEdgeCutQueriedPorts, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hq, heq⟩
    have hd : d = c := congrArg Prod.fst heq
    simpa [hd] using hq
  · intro hq
    exact ⟨c, hq, rfl⟩

theorem parafermionicCoverFiniteEdgeCutQueriedTrue_mem_iff (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n) :
    (c, true) ∈
        (parafermionicCoverFiniteEdgeCutQueriedPorts n e).image (fun d => (d, false)) ↔ False := by
  classical
  simp only [parafermionicCoverFiniteEdgeCutQueriedPorts, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, _, heq⟩
    have hb := congrArg Prod.snd heq
    exact Bool.noConfusion hb
  · intro h
    exact False.elim h

theorem parafermionicCoverFiniteEdgeCutCornerTerminals_false_mem_iff
    (n : ℕ) (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) :
    (c, false) ∈ parafermionicCoverFiniteEdgeCutCornerTerminals n hn ↔ False := by
  simp [parafermionicCoverFiniteEdgeCutCornerTerminals]

theorem parafermionicCoverFiniteEdgeCutCornerTerminals_true_mem_iff
    (n : ℕ) (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) :
    (c, true) ∈ parafermionicCoverFiniteEdgeCutCornerTerminals n hn ↔
      c = parafermionicCoverFiniteOriginCornerPort n hn ∨
        c = parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn) := by
  simp [parafermionicCoverFiniteEdgeCutCornerTerminals]

theorem parafermionicCoverFiniteEdgeCutDegreeOne_carrier (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e =
      (parafermionicCoverFiniteEdgeCutQueriedPorts n e).image (fun c => (c, false)) ∪
        parafermionicCoverFiniteEdgeCutCornerTerminals n hn := by
  classical
  ext v
  rcases v with ⟨c, b⟩
  cases b
  · simp only [parafermionicCoverFiniteEdgeCutDegreeOneVertices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.mem_union,
      parafermionicCoverFiniteEdgeCutQueriedFalse_mem_iff,
      parafermionicCoverFiniteEdgeCutCornerTerminals_false_mem_iff]
    rw [parafermionicCoverFiniteEdgeCutGraph_degree_false]
    by_cases hq : parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e
    · simp [hq]
    · simp [hq]
  · simp only [parafermionicCoverFiniteEdgeCutDegreeOneVertices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.mem_union,
      parafermionicCoverFiniteEdgeCutQueriedTrue_mem_iff,
      parafermionicCoverFiniteEdgeCutCornerTerminals_true_mem_iff]
    rw [parafermionicCoverFiniteEdgeCutDegreeOne_true_iff]
    simp only [false_or]

theorem parafermionicCoverFiniteEdgeCutQueriedPorts_card (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutQueriedPorts n e).card = 4 := by
  classical
  obtain ⟨c, hc⟩ := parafermionicCoverFinitePort_exists_for_edge n e
  have hbox : ∀ v ∈ (parafermionicCoverPortEdge c.1).1,
      v ∈ parafermionicCoverBoxVertices n := by
    intro v hv
    rw [hc] at hv
    exact parafermionicCoverFiniteEdgeEmbedding_endpoints_mem n e v hv
  obtain ⟨c₀, c₁, c₂, c₃, hc₀, hc₁, hc₂, hc₃⟩ :=
    parafermionicCoverPort_four_mem_finite n c.1 hbox
  have hq₀ : parafermionicCoverPortEdge c₀.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
    rw [hc₀]
    exact hc
  have hq₁ : parafermionicCoverPortEdge c₁.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
    apply Subtype.ext
    calc
      (parafermionicCoverPortEdge c₁.1).val =
          (parafermionicCoverPortEdge (parafermionicCoverOpenPair c.1)).val := by rw [hc₁]
      _ = (parafermionicCoverPortEdge c.1).val := parafermionicCoverOpenPair_edge_val_eq c.1
      _ = (parafermionicCoverFiniteEdgeEmbedding n e).val := congrArg Subtype.val hc
  have hq₂ : parafermionicCoverPortEdge c₂.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
    apply Subtype.ext
    calc
      (parafermionicCoverPortEdge c₂.1).val =
          (parafermionicCoverPortEdge (parafermionicCoverClosedPair c.1)).val := by rw [hc₂]
      _ = (parafermionicCoverPortEdge c.1).val := parafermionicCoverClosedPair_edge_val_eq c.1
      _ = (parafermionicCoverFiniteEdgeEmbedding n e).val := congrArg Subtype.val hc
  have hq₃ : parafermionicCoverPortEdge c₃.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
    apply Subtype.ext
    calc
      (parafermionicCoverPortEdge c₃.1).val =
          (parafermionicCoverPortEdge
            (parafermionicCoverOpenPair (parafermionicCoverClosedPair c.1))).val := by rw [hc₃]
      _ = (parafermionicCoverPortEdge (parafermionicCoverClosedPair c.1)).val :=
        parafermionicCoverOpenPair_edge_val_eq _
      _ = (parafermionicCoverPortEdge c.1).val := parafermionicCoverClosedPair_edge_val_eq c.1
      _ = (parafermionicCoverFiniteEdgeEmbedding n e).val := congrArg Subtype.val hc
  have hset : parafermionicCoverFiniteEdgeCutQueriedPorts n e = {c₀, c₁, c₂, c₃} := by
    ext d
    simp only [parafermionicCoverFiniteEdgeCutQueriedPorts, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hd
      have he : parafermionicCoverPortEdge d.1 = parafermionicCoverPortEdge c₀.1 :=
        hd.trans hq₀.symm
      rcases (parafermionicCoverPortEdge_eq_iff_four c₀.1 d.1).mp he with h | h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext (by
          calc
            d.1 = parafermionicCoverOpenPair c₀.1 := h
            _ = parafermionicCoverOpenPair c.1 := congrArg parafermionicCoverOpenPair hc₀
            _ = c₁.1 := hc₁.symm)))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by
          calc
            d.1 = parafermionicCoverClosedPair c₀.1 := h
            _ = parafermionicCoverClosedPair c.1 := congrArg parafermionicCoverClosedPair hc₀
            _ = c₂.1 := hc₂.symm))))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by
          calc
            d.1 = parafermionicCoverOpenPair (parafermionicCoverClosedPair c₀.1) := h
            _ = parafermionicCoverOpenPair (parafermionicCoverClosedPair c.1) :=
              congrArg (fun x => parafermionicCoverOpenPair (parafermionicCoverClosedPair x)) hc₀
            _ = c₃.1 := hc₃.symm))))
    · intro hd
      rcases hd with h | h | h | h
      · simpa [h] using hq₀
      · simpa [h] using hq₁
      · simpa [h] using hq₂
      · simpa [h] using hq₃
  have h01 : c₀ ≠ c₁ := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hc₀, hc₁] at hv
    exact (parafermionicCoverOpenPair_ne c.1) hv.symm
  have h02 : c₀ ≠ c₂ := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hc₀, hc₂] at hv
    exact (parafermionicCoverClosedPair_ne c.1) hv.symm
  have h03 : c₀ ≠ c₃ := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hc₀, hc₃] at hv
    exact (parafermionicCoverPort_four_pairwise_ne c.1).2.2.1 hv.symm
  have h12 : c₁ ≠ c₂ := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hc₁, hc₂] at hv
    exact (parafermionicCoverPort_four_pairwise_ne c.1).2.2.2.1 hv
  have h13 : c₁ ≠ c₃ := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hc₁, hc₃] at hv
    exact (parafermionicCoverPort_four_pairwise_ne c.1).2.2.2.2.1 hv.symm
  have h23 : c₂ ≠ c₃ := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hc₂, hc₃] at hv
    exact (parafermionicCoverPort_four_pairwise_ne c.1).2.2.2.2.2 hv.symm
  rw [hset]
  simp [h01, h02, h03, h12, h13, h23]

theorem parafermionicCoverFiniteEdgeCutDegreeOneVertices_card (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e).card = 6 := by
  classical
  rw [parafermionicCoverFiniteEdgeCutDegreeOne_carrier]
  have hquery :
      ((parafermionicCoverFiniteEdgeCutQueriedPorts n e).image (fun c => (c, false))).card = 4 := by
    rw [Finset.card_image_iff.mpr]
    · exact parafermionicCoverFiniteEdgeCutQueriedPorts_card n e
    · intro a ha b hb hab
      exact congrArg Prod.fst hab
  have hcorner_ne :
      parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn) ≠
        parafermionicCoverFiniteOriginCornerPort n hn :=
    parafermionicCoverFiniteCornerPairPerm_no_fixed_points n _
  have hcorner : (parafermionicCoverFiniteEdgeCutCornerTerminals n hn).card = 2 := by
    change ({(parafermionicCoverFiniteOriginCornerPort n hn, true),
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true)} :
        Finset (ParafermionicCoverFinitePort n × Bool)).card = 2
    exact Finset.card_pair (by intro h; exact hcorner_ne (congrArg Prod.fst h).symm)
  have hdisjoint : Disjoint
      ((parafermionicCoverFiniteEdgeCutQueriedPorts n e).image (fun c => (c, false)))
      (parafermionicCoverFiniteEdgeCutCornerTerminals n hn) := by
    apply Finset.disjoint_left.mpr
    intro v hvq hvc
    rcases Finset.mem_image.mp hvq with ⟨c, _, rfl⟩
    simp [parafermionicCoverFiniteEdgeCutCornerTerminals] at hvc
  rw [Finset.card_union_of_disjoint hdisjoint, hquery, hcorner]

theorem parafermionicCoverFiniteEdgeCutGraph_degree_le_two (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (v : ParafermionicCoverFinitePort n × Bool) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree v ≤ 2 := by
  rcases v with ⟨c, b⟩
  cases b
  · rw [parafermionicCoverFiniteEdgeCutGraph_degree_false]
    split_ifs <;> omega
  · let C := parafermionicCoverFiniteCornerPairPerm n
    let s := parafermionicCoverFiniteOriginCornerPort n hn
    have hC : Function.Involutive C := parafermionicCoverFiniteCornerPairPerm_involutive n
    have hCfree : ∀ p, C p ≠ p := parafermionicCoverFiniteCornerPairPerm_no_fixed_points n
    have hfixed : pairingSingleCutPerm C s hC c = c ↔ c = s ∨ c = C s :=
      pairingSingleCutPerm_fixed_iff C s c hC hCfree
    by_cases hpair : pairingSingleCutPerm C s hC c = c
    · rw [parafermionicCoverFiniteEdgeCutGraph_degree_true_of_fixed n hn A e c hpair]
      omega
    · rw [parafermionicCoverFiniteEdgeCutGraph_degree_true_of_not_fixed n hn A e c hpair]

theorem parafermionicCoverFiniteEdgeCutGraph_existsUnique_partner
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (s : ParafermionicCoverFinitePort n × Bool)
    (hs : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree s = 1) :
    ∃! t : ParafermionicCoverFinitePort n × Bool,
      t ≠ s ∧
        (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree t = 1 ∧
        (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable s t := by
  exact existsUnique_ne_reachable_degree_one_of_degree_le_two
    (parafermionicCoverFiniteEdgeCutGraph n hn A e)
    (parafermionicCoverFiniteEdgeCutGraph_degree_le_two n hn A e) s hs

end
end PottsContinuity.Thm4
