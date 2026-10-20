module

public import PottsContinuity.Thm1.FiniteESSignatureQuotient
public import PottsContinuity.Thm1.FiniteESCylinder
public import PottsContinuity.Thm1.ShellFullSignatures

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance pottsESSignatureLimitObsFintype (observed : Finset (ℤ × ℤ)) :
    Fintype (pottsESObservedSite observed) := Fintype.ofFinite _

local instance pottsESSignatureLimitPairFintype (observed : Finset (ℤ × ℤ)) :
    Fintype (pottsESObservedPair observed) := Fintype.ofFinite _

local instance pottsESSignatureLimitPairDecidableEq (observed : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESObservedPair observed) := Classical.decEq _

local instance pottsESSignatureLimitSiteDecidableEq (observed : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESObservedSite observed) := Classical.decEq _

def pottsESStatusPositivePairs (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := by
  classical
  exact ((Finset.univ : Finset (pottsESObservedPair observed)).filter
    (fun p => s.1 p = true)).image (fun p => (p.1.1, p.2.1))

def pottsESStatusNegativePairs (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := by
  classical
  exact ((Finset.univ : Finset (pottsESObservedPair observed)).filter
    (fun p => s.1 p = false)).image (fun p => (p.1.1, p.2.1))

def pottsESStatusGhostPositive (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.univ : Finset (pottsESObservedSite observed)).filter
    (fun x => s.2 x = true)).image Subtype.val

def pottsESStatusGhostNegative (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.univ : Finset (pottsESObservedSite observed)).filter
    (fun x => s.2 x = false)).image Subtype.val

def pottsESStatusAtomEvent (V observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) : Set LatticeConfiguration :=
  pottsESLatticeFullSignatureEvent V
    (pottsESStatusPositivePairs observed s)
    (pottsESStatusNegativePairs observed s)
    (pottsESStatusGhostPositive observed s)
    (pottsESStatusGhostNegative observed s)

theorem pottsESLatticePairIntersectionEvent_mem_iff
    (V : Finset (ℤ × ℤ)) (P : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (ω : LatticeConfiguration) :
    ω ∈ pottsESLatticePairIntersectionEvent V P ↔
      ∀ p ∈ P, ω ∈ pottsESLatticePairRelationEvent V p.1 p.2 := by
  simp [pottsESLatticePairIntersectionEvent, Set.mem_iInter]

theorem pottsESLatticePairPatternEvent_mem_iff
    (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (ω : LatticeConfiguration) :
    ω ∈ pottsESLatticePairPatternEvent V Positive Negative ↔
      (∀ p ∈ Positive, ω ∈ pottsESLatticePairRelationEvent V p.1 p.2) ∧
      (∀ p ∈ Negative, ω ∉ pottsESLatticePairRelationEvent V p.1 p.2) := by
  change (ω ∈ pottsESLatticePairIntersectionEvent V Positive ∧
    ω ∉ ⋃ p ∈ Negative,
      pottsESLatticePairIntersectionEvent V (Positive ∪ {p})) ↔ _
  rw [pottsESLatticePairIntersectionEvent_mem_iff]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨hpos, hnot⟩
    refine ⟨hpos, ?_⟩
    intro p hp hrel
    apply hnot
    refine ⟨p, hp, ?_⟩
    apply (pottsESLatticePairIntersectionEvent_mem_iff V (Positive ∪ {p}) ω).2
    intro z hz
    rcases Finset.mem_union.mp hz with hzPos | hzP
    · exact hpos z hzPos
    · have hzp : z = p := Finset.mem_singleton.mp hzP
      subst z
      exact hrel
  · rintro ⟨hpos, hneg⟩
    refine ⟨hpos, ?_⟩
    intro hex
    rcases hex with ⟨p, hp, hInter⟩
    apply hneg p hp
    exact (pottsESLatticePairIntersectionEvent_mem_iff V (Positive ∪ {p}) ω).1 hInter p
      (Finset.mem_union_right _ (Finset.mem_singleton_self p))

theorem pottsESLatticePairGhostPatternEvent_mem_iff
    (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostSites : Finset (ℤ × ℤ)) (ω : LatticeConfiguration) :
    ω ∈ pottsESLatticePairGhostPatternEvent V Positive Negative GhostSites ↔
      (∀ p ∈ Positive, ω ∈ pottsESLatticePairRelationEvent V p.1 p.2) ∧
      (∀ p ∈ Negative, ω ∉ pottsESLatticePairRelationEvent V p.1 p.2) ∧
      (∀ x ∈ GhostSites, ω ∈ pottsESLatticeExitEventFrom V x) := by
  change (ω ∈ pottsESLatticePairPatternEvent V Positive Negative ∧
    ω ∈ ⋂ x ∈ GhostSites, pottsESLatticeExitEventFrom V x) ↔ _
  rw [pottsESLatticePairPatternEvent_mem_iff]
  simp only [Set.mem_iInter]
  tauto

theorem pottsESLatticeFullSignatureEvent_mem_iff
    (V : Finset (ℤ × ℤ))
    (Positive Negative : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (GhostPositive GhostNegative : Finset (ℤ × ℤ)) (ω : LatticeConfiguration) :
    ω ∈ pottsESLatticeFullSignatureEvent V Positive Negative
        GhostPositive GhostNegative ↔
      (∀ p ∈ Positive, ω ∈ pottsESLatticePairRelationEvent V p.1 p.2) ∧
      (∀ p ∈ Negative, ω ∉ pottsESLatticePairRelationEvent V p.1 p.2) ∧
      (∀ x ∈ GhostPositive, ω ∈ pottsESLatticeExitEventFrom V x) ∧
      (∀ x ∈ GhostNegative, ω ∉ pottsESLatticeExitEventFrom V x) := by
  change (ω ∈ pottsESLatticePairGhostPatternEvent V Positive Negative GhostPositive ∧
    ω ∉ ⋃ x ∈ GhostNegative,
      pottsESLatticePairGhostPatternEvent V Positive Negative (GhostPositive ∪ {x})) ↔ _
  simp only [Set.mem_iUnion]
  rw [pottsESLatticePairGhostPatternEvent_mem_iff]
  constructor
  · rintro ⟨⟨hpos, hneg, hghostpos⟩, hnot⟩
    refine ⟨hpos, hneg, hghostpos, ?_⟩
    intro x hx hxreach
    apply hnot
    refine ⟨x, hx, ?_⟩
    apply (pottsESLatticePairGhostPatternEvent_mem_iff V Positive Negative
      (GhostPositive ∪ {x}) ω).2
    refine ⟨hpos, hneg, ?_⟩
    intro y hy
    rcases Finset.mem_union.mp hy with hypos | hyx
    · exact hghostpos y hypos
    · have hyEq : y = x := Finset.mem_singleton.mp hyx
      subst y
      exact hxreach
  · rintro ⟨hpos, hneg, hghostpos, hghostneg⟩
    refine ⟨⟨hpos, hneg, hghostpos⟩, ?_⟩
    intro hex
    rcases hex with ⟨x, hx, hmore⟩
    have hmore' := (pottsESLatticePairGhostPatternEvent_mem_iff V Positive Negative
      (GhostPositive ∪ {x}) ω).1 hmore
    exact hghostneg x hx (hmore'.2.2 x
      (Finset.mem_union_right _ (Finset.mem_singleton_self x)))

private theorem pottsESStatusPositivePairs_mem_iff
    (observed : Finset (ℤ × ℤ)) (s : pottsESStatusSignature observed)
    (p : pottsESObservedPair observed) :
    (p.1.1, p.2.1) ∈ pottsESStatusPositivePairs observed s ↔ s.1 p = true := by
  unfold pottsESStatusPositivePairs
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨p', hp', heq⟩
    have hpEq : p' = p := by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst heq
      · apply Subtype.ext
        exact congrArg Prod.snd heq
    subst p'
    exact (Finset.mem_filter.mp hp').2
  · intro hb
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

private theorem pottsESStatusNegativePairs_mem_iff
    (observed : Finset (ℤ × ℤ)) (s : pottsESStatusSignature observed)
    (p : pottsESObservedPair observed) :
    (p.1.1, p.2.1) ∈ pottsESStatusNegativePairs observed s ↔ s.1 p = false := by
  unfold pottsESStatusNegativePairs
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨p', hp', heq⟩
    have hpEq : p' = p := by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst heq
      · apply Subtype.ext
        exact congrArg Prod.snd heq
    subst p'
    exact (Finset.mem_filter.mp hp').2
  · intro hb
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

private theorem pottsESStatusGhostPositive_mem_iff
    (observed : Finset (ℤ × ℤ)) (s : pottsESStatusSignature observed)
    (x : pottsESObservedSite observed) :
    x.1 ∈ pottsESStatusGhostPositive observed s ↔ s.2 x = true := by
  unfold pottsESStatusGhostPositive
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨x', hx', heq⟩
    have hxEq : x' = x := Subtype.ext heq
    subst x'
    exact (Finset.mem_filter.mp hx').2
  · intro hb
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

private theorem pottsESStatusGhostNegative_mem_iff
    (observed : Finset (ℤ × ℤ)) (s : pottsESStatusSignature observed)
    (x : pottsESObservedSite observed) :
    x.1 ∈ pottsESStatusGhostNegative observed s ↔ s.2 x = false := by
  unfold pottsESStatusGhostNegative
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨x', hx', heq⟩
    have hxEq : x' = x := Subtype.ext heq
    subst x'
    exact (Finset.mem_filter.mp hx').2
  · intro hb
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

theorem pottsESStatusAtomEvent_mem_iff_statusConditions
    (V observed : Finset (ℤ × ℤ)) (s : pottsESStatusSignature observed)
    (ω : LatticeConfiguration) :
    ω ∈ pottsESStatusAtomEvent V observed s ↔
      (∀ p : pottsESObservedPair observed,
        (ω ∈ pottsESLatticePairRelationEvent V p.1.1 p.2.1 ↔ s.1 p = true)) ∧
      (∀ x : pottsESObservedSite observed,
        (ω ∈ pottsESLatticeExitEventFrom V x.1 ↔ s.2 x = true)) := by
  rw [pottsESStatusAtomEvent, pottsESLatticeFullSignatureEvent_mem_iff]
  constructor
  · rintro ⟨hpos, hneg, hghostpos, hghostneg⟩
    constructor
    · intro p
      constructor
      · intro hp
        cases hb : s.1 p with
        | false => exact (hneg (p.1.1, p.2.1)
            ((pottsESStatusNegativePairs_mem_iff observed s p).2 hb) hp).elim
        | true => rfl
      · intro hb
        cases hs : s.1 p with
        | false => simp [hs] at hb
        | true =>
            have hrel := hpos (p.1.1, p.2.1)
              ((pottsESStatusPositivePairs_mem_iff observed s p).2 hs)
            simpa only [Prod.fst, Prod.snd] using hrel
    · intro x
      constructor
      · intro hx
        cases hb : s.2 x with
        | false => exact (hghostneg x.1
            ((pottsESStatusGhostNegative_mem_iff observed s x).2 hb) hx).elim
        | true => rfl
      · intro hb
        cases hs : s.2 x with
        | false => simp [hs] at hb
        | true =>
            exact hghostpos x.1
              ((pottsESStatusGhostPositive_mem_iff observed s x).2 hs)
  · rintro ⟨hPairs, hGhosts⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro pair hp
      rcases Finset.mem_image.mp hp with ⟨p, hpFilter, hEq⟩
      have hb := (Finset.mem_filter.mp hpFilter).2
      have hrel := (hPairs p).2 hb
      rw [← hEq]
      simpa only [Prod.fst, Prod.snd] using hrel
    · intro pair hp hrel
      rcases Finset.mem_image.mp hp with ⟨p, hpFilter, hEq⟩
      have hbFalse := (Finset.mem_filter.mp hpFilter).2
      rw [← hEq] at hrel
      have hrel' : ω ∈ pottsESLatticePairRelationEvent V p.1.1 p.2.1 := by
        simpa only [Prod.fst, Prod.snd] using hrel
      have hbTrue := (hPairs p).1 hrel'
      simp [hbFalse] at hbTrue
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨x, hxFilter, hEq⟩
      have hb := (Finset.mem_filter.mp hxFilter).2
      rw [← hEq]
      exact (hGhosts x).2 hb
    · intro x hx hrel
      rcases Finset.mem_image.mp hx with ⟨x, hxFilter, hEq⟩
      have hbFalse := (Finset.mem_filter.mp hxFilter).2
      rw [← hEq] at hrel
      have hrel' : ω ∈ pottsESLatticeExitEventFrom V x.1 := hrel
      have hbTrue := (hGhosts x).1 hrel'
      simp [hbFalse] at hbTrue

theorem pottsESObservedStatusSignature_mem_atom_iff
    (V observed : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (s : pottsESStatusSignature observed) :
    pottsESShellBondExtension V A ∈ pottsESStatusAtomEvent V observed s ↔
      pottsESObservedStatusSignature V observed A = s := by
  classical
  rw [pottsESStatusAtomEvent_mem_iff_statusConditions]
  constructor
  · intro h
    have hPair : ∀ p : pottsESObservedPair observed,
        s.1 p = (pottsESObservedStatusSignature V observed A).1 p := by
      intro p
      by_cases hr : pottsESShellBondExtension V A ∈
          pottsESLatticePairRelationEvent V p.1.1 p.2.1
      · have hs := (h.1 p).1 hr
        simp [pottsESObservedStatusSignature, hr, hs]
      · have hs : s.1 p = false := by
          cases hb : s.1 p with
          | false => rfl
          | true => exact False.elim (hr ((h.1 p).2 hb))
        simp [pottsESObservedStatusSignature, hr, hs]
    have hGhost : ∀ x : pottsESObservedSite observed,
        s.2 x = (pottsESObservedStatusSignature V observed A).2 x := by
      intro x
      by_cases hr : pottsESShellBondExtension V A ∈
          pottsESLatticeExitEventFrom V x.1
      · have hs := (h.2 x).1 hr
        simp [pottsESObservedStatusSignature, hr, hs]
      · have hs : s.2 x = false := by
          cases hb : s.2 x with
          | false => rfl
          | true => exact False.elim (hr ((h.2 x).2 hb))
        simp [pottsESObservedStatusSignature, hr, hs]
    apply Prod.ext
    · exact (funext hPair).symm
    · exact (funext hGhost).symm
  · intro hs
    constructor
    · intro p
      have hsig := congrFun (congrArg Prod.fst hs) p
      change decide (pottsESShellBondExtension V A ∈
        pottsESLatticePairRelationEvent V p.1.1 p.2.1) = s.1 p at hsig
      change (pottsESShellBondExtension V A ∈
        pottsESLatticePairRelationEvent V p.1.1 p.2.1) ↔ s.1 p = true
      rw [← hsig]
      simp only [decide_eq_true_eq]
    · intro x
      have hsig := congrFun (congrArg Prod.snd hs) x
      change decide (pottsESShellBondExtension V A ∈
        pottsESLatticeExitEventFrom V x.1) = s.2 x at hsig
      change (pottsESShellBondExtension V A ∈
        pottsESLatticeExitEventFrom V x.1) ↔ s.2 x = true
      rw [← hsig]
      simp only [decide_eq_true_eq]

end

end PottsContinuity.Thm1
