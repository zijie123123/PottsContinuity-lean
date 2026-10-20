-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPairingSimplicity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.GraphWalkPathSubstitutionSimple
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingRouteInteriorShape
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerInterior
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph
open PottsContinuity.FKC.FiniteFK

noncomputable abbrev refinedPairingRoute {n : ℕ} (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :=
  parafermionicCoverRefinedPairingRoute n hn A h

/-- The actual walk obtained by replacing every edge of the corner-cut pairing
walk with its canonical refined route. -/
noncomputable def parafermionicCoverRefinedPairingWalk (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v) :
    parafermionicCoverGraph.Walk
      (parafermionicCoverRefinedPairingEmbedding u)
      (parafermionicCoverRefinedPairingEmbedding v) :=
  graphWalkSubstitute (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
    parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
    (fun {_a _b} h => parafermionicCoverRefinedPairingRoute n hn A h) p

private theorem refinedPairingRoute_tail_getLast (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    ∃ hne : (refinedPairingRoute hn A h).support.tail ≠ [],
      (refinedPairingRoute hn A h).support.tail.getLast hne =
        parafermionicCoverRefinedPairingEmbedding v := by
  have hpositive : 0 < (refinedPairingRoute hn A h).length := by
    by_contra hnot
    have hzero : (refinedPairingRoute hn A h).length = 0 := by omega
    have heq : parafermionicCoverRefinedPairingEmbedding u =
        parafermionicCoverRefinedPairingEmbedding v :=
      Walk.eq_of_length_eq_zero hzero
    exact h.ne (parafermionicCoverRefinedPairingEmbedding_injective n heq)
  have htailLength : (refinedPairingRoute hn A h).support.tail.length =
      (refinedPairingRoute hn A h).length := by
    rw [List.length_tail, Walk.length_support]
    omega
  have hne : (refinedPairingRoute hn A h).support.tail ≠ [] := by
    intro hnil
    have hlen : (refinedPairingRoute hn A h).support.tail.length = 0 := by simp [hnil]
    rw [htailLength] at hlen
    omega
  refine ⟨hne, ?_⟩
  simp

private theorem refinedPairingRoute_interior_not_embedding (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (refinedPairingRoute hn A h).support.tail.dropLast) :
    ∀ d : ParafermionicCoverFinitePort n, ∀ b : Bool,
      z ≠ parafermionicCoverRefinedPairingEmbedding (d, b) := by
  intro d b
  have hshape := parafermionicCoverRefinedPairingRoute_interior n hn A h
  rcases u with ⟨c, bc⟩
  rcases v with ⟨e, be⟩
  rw [hshape] at hz
  simp only at hz
  cases bc <;> cases be
  · by_cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) c.1
    · simp [hs] at hz
    · simp [hs] at hz
      rcases hz with heq
      subst z
      exact parafermionicCoverRefinedClosedCapMiddle_ne_embedding c d b
  · simp at hz
  · simp at hz
  · simp only [List.mem_cons, List.not_mem_nil] at hz
    rcases hz with hmid₁ | hmid₂ | hmid₃ | hfalse
    · rcases hmid₁ with rfl
      have hcorner : parafermionicCoverRefinedCornerMid₁ c ∈
          parafermionicCoverRefinedCornerWalkInterior c := by
        rw [parafermionicCoverRefinedCornerWalkInterior_eq]
        simp
      exact parafermionicCoverRefinedCornerInterior_ne_portEmbedding c d b hcorner
    · rcases hmid₂ with rfl
      have hcorner : parafermionicCoverRefinedCornerElbow c ∈
          parafermionicCoverRefinedCornerWalkInterior c := by
        rw [parafermionicCoverRefinedCornerWalkInterior_eq]
        simp
      exact parafermionicCoverRefinedCornerInterior_ne_portEmbedding c d b hcorner
    · rcases hmid₃ with rfl
      have hcorner : parafermionicCoverRefinedCornerMid₂ c ∈
          parafermionicCoverRefinedCornerWalkInterior c := by
        rw [parafermionicCoverRefinedCornerWalkInterior_eq]
        simp
      exact parafermionicCoverRefinedCornerInterior_ne_portEmbedding c d b hcorner
    · contradiction

private theorem refinedPairingRoute_range (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (refinedPairingRoute hn A h).support.tail)
    (hrange : z ∈ Set.range (@parafermionicCoverRefinedPairingEmbedding n)) :
    z = parafermionicCoverRefinedPairingEmbedding v := by
  obtain ⟨hne, hlast⟩ := refinedPairingRoute_tail_getLast n hn A h
  rcases hrange with ⟨a, ha⟩
  by_cases hzlast : z = (refinedPairingRoute hn A h).support.tail.getLast hne
  · exact hzlast.trans hlast
  · have hzint := List.mem_dropLast_of_mem_of_ne_getLast hz hzlast
    exact False.elim (refinedPairingRoute_interior_not_embedding n hn A h hzint a.1 a.2 ha.symm)

private theorem refinedPairingRoute_interior_classification (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (refinedPairingRoute hn A h).support.tail.dropLast) :
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
  · have hcorner := parafermionicCoverRefinedPairingRoute_true_true_endpoint
      n hn A c d h
    have hzlist : z ∈ [parafermionicCoverRefinedCornerMid₁ c.1,
        parafermionicCoverRefinedCornerElbow c.1,
        parafermionicCoverRefinedCornerMid₂ c.1] := by
      simpa using hz
    have hzcorner : z ∈ parafermionicCoverRefinedCornerWalkInterior c.1 :=
      (parafermionicCoverRefinedCornerWalkInterior_eq c.1).symm ▸ hzlist
    exact Or.inr ⟨rfl, rfl, hcorner, hzcorner⟩

private theorem refinedPairingRoute_edge_eq_of_sharedInterior (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {a b c d : ParafermionicCoverFinitePort n × Bool}
    (h₁ : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj a b)
    (h₂ : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj c d)
    {z : ParafermionicCoverVertex}
    (hz₁ : z ∈ (refinedPairingRoute hn A h₁).support.tail.dropLast)
    (hz₂ : z ∈ (refinedPairingRoute hn A h₂).support.tail.dropLast) :
    s(a,b) = s(c,d) := by
  have h₁class := refinedPairingRoute_interior_classification n hn A h₁ hz₁
  have h₂class := refinedPairingRoute_interior_classification n hn A h₂ hz₂
  rcases h₁class with ⟨ha0, hb0, hstate₁, hpair₁, hmid₁⟩ |
    ⟨ha1, hb1, hpair₁, hcorner₁⟩
  · rcases h₂class with ⟨hc0, hd0, hstate₂, hpair₂, hmid₂⟩ |
      ⟨hc1, hd1, hpair₂, hcorner₂⟩
    · have hmidEq := hmid₁.symm.trans hmid₂
      have hclass := (parafermionicCoverRefinedClosedCapMiddle_eq_iff
        a.1.1 c.1.1).mp hmidEq
      have hportEq : a.1 = c.1 ∨ c.1.1 = parafermionicCoverClosedPair a.1.1 := by
        rcases hclass with hsame | hrev
        · exact Or.inl (Subtype.ext hsame.symm)
        · exact Or.inr hrev
      rcases hportEq with hsame | hrev
      · have hsource : a = c := by exact Prod.ext hsame (ha0.trans hc0.symm)
        have htarget : b = d := by
          apply Prod.ext
          · apply Subtype.ext
            calc
              b.1.1 = parafermionicCoverClosedPair a.1.1 := hpair₁
              _ = parafermionicCoverClosedPair c.1.1 := by rw [hsame]
              _ = d.1.1 := hpair₂.symm
          · exact hb0.trans hd0.symm
        exact Sym2.eq_iff.mpr (Or.inl ⟨hsource, htarget⟩)
      · have hsourceRaw : c.1.1 = parafermionicCoverClosedPair a.1.1 := hrev
        have htargetRaw : d.1.1 = a.1.1 := by
          calc
            d.1.1 = parafermionicCoverClosedPair c.1.1 := hpair₂
            _ = parafermionicCoverClosedPair (parafermionicCoverClosedPair a.1.1) := by rw [hsourceRaw]
            _ = a.1.1 := parafermionicCoverClosedPair_involutive a.1.1
        have hsource : a = d := by
          apply Prod.ext
          · apply Subtype.ext
            exact htargetRaw.symm
          · exact ha0.trans hd0.symm
        have htarget : b = c := by
          apply Prod.ext
          · apply Subtype.ext
            exact hpair₁.trans hsourceRaw.symm
          · exact hb0.trans hc0.symm
        exact Sym2.eq_iff.mpr (Or.inr ⟨hsource, htarget⟩)
    · exfalso
      have hcap : z = parafermionicCoverRefinedClosedCapMiddle a.1.1 := hmid₁
      exact (parafermionicCoverRefinedCornerInterior_ne_closedCapMiddle c.1.1 a.1.1
        hcorner₂) hcap
  · rcases h₂class with ⟨hc0, hd0, hstate₂, hpair₂, hmid₂⟩ |
      ⟨hc1, hd1, hpair₂, hcorner₂⟩
    · exfalso
      have hcap : z = parafermionicCoverRefinedClosedCapMiddle c.1.1 := hmid₂
      exact (parafermionicCoverRefinedCornerInterior_ne_closedCapMiddle a.1.1 c.1.1
        hcorner₁) hcap
    · have hclass := parafermionicCoverRefinedCornerInterior_eq_classification
        a.1.1 c.1.1 hcorner₁ hcorner₂ rfl
      have hportEq : c.1 = a.1 ∨ c.1.1 = parafermionicCoverCornerPair a.1.1 := by
        rcases hclass with hsame | hrev
        · exact Or.inl (Subtype.ext hsame)
        · exact Or.inr hrev
      rcases hportEq with hsame | hrev
      · have hsource : a = c := by exact Prod.ext hsame.symm (ha1.trans hc1.symm)
        have htarget : b = d := by
          apply Prod.ext
          · apply Subtype.ext
            calc
              b.1.1 = parafermionicCoverCornerPair a.1.1 := hpair₁
              _ = parafermionicCoverCornerPair c.1.1 := by rw [hsame.symm]
              _ = d.1.1 := hpair₂.symm
          · exact hb1.trans hd1.symm
        exact Sym2.eq_iff.mpr (Or.inl ⟨hsource, htarget⟩)
      · have hsourceRaw : c.1.1 = parafermionicCoverCornerPair a.1.1 := hrev
        have htargetRaw : d.1.1 = a.1.1 := by
          calc
            d.1.1 = parafermionicCoverCornerPair c.1.1 := hpair₂
            _ = parafermionicCoverCornerPair (parafermionicCoverCornerPair a.1.1) := by rw [hsourceRaw]
            _ = a.1.1 := parafermionicCoverCornerPair_involutive a.1.1
        have hsource : a = d := by
          apply Prod.ext
          · apply Subtype.ext
            exact htargetRaw.symm
          · exact ha1.trans hd1.symm
        have htarget : b = c := by
          apply Prod.ext
          · apply Subtype.ext
            exact hpair₁.trans hsourceRaw.symm
          · exact hb1.trans hc1.symm
        exact Sym2.eq_iff.mpr (Or.inr ⟨hsource, htarget⟩)

private theorem refinedPairingRoute_interiors_disjoint (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {a b c d : ParafermionicCoverFinitePort n × Bool}
    (h₁ : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj a b)
    (h₂ : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj c d)
    (hedge : s(a,b) ≠ s(c,d)) :
    List.Disjoint ((refinedPairingRoute hn A h₁).support.tail.dropLast)
      ((refinedPairingRoute hn A h₂).support.tail.dropLast) := by
  apply List.disjoint_left.mpr
  intro z hz₁ hz₂
  exact hedge (refinedPairingRoute_edge_eq_of_sharedInterior n hn A h₁ h₂ hz₁ hz₂)

/-- Replacing every edge by its actual refined route preserves simplicity for
all actual walks in the finite corner-cut pairing graph. -/
theorem parafermionicCoverRefinedPairingWalk_isPath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (hp : p.IsPath) :
    (parafermionicCoverRefinedPairingWalk n hn A p).IsPath := by
  change (graphWalkSubstitute
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
    parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
    (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h) p).IsPath
  exact graphWalkSubstitute_isPath
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
    parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
    (parafermionicCoverRefinedPairingEmbedding_injective n)
    (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h)
    (by intro a b h; exact parafermionicCoverRefinedPairingRoute_isPath n hn A h)
    (by intro a b h z hz hr; exact refinedPairingRoute_range n hn A h hz hr)
    (by intro a b c d h₁ h₂ hedge; exact refinedPairingRoute_interiors_disjoint n hn A h₁ h₂ hedge)
    p hp

/-- Replacing every edge by its actual refined route preserves an actual
simple cycle without changing the source cycle's ordered edge sequence. -/
theorem parafermionicCoverRefinedPairingWalk_isCycle (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u u)
    (hp : p.IsCycle) :
    (parafermionicCoverRefinedPairingWalk n hn A p).IsCycle := by
  change (graphWalkSubstitute
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
    parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
    (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h) p).IsCycle
  exact graphWalkSubstitute_isCycle
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
    parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
    (parafermionicCoverRefinedPairingEmbedding_injective n)
    (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h)
    (by intro a b h; exact parafermionicCoverRefinedPairingRoute_isPath n hn A h)
    (by intro a b h z hz hr; exact refinedPairingRoute_range n hn A h hz hr)
    (by intro a b c d h₁ h₂ hedge; exact refinedPairingRoute_interiors_disjoint n hn A h₁ h₂ hedge)
    p hp

end PottsContinuity.FKC.Medial
