module

public import PottsContinuity.Thm1.FiniteESPatternCount
public import PottsContinuity.Thm1.ShellPairConnectivity
public import PottsContinuity.Thm1.ShellPairEvent
public import PottsContinuity.Thm1.FiniteESSignatureClasses

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance pottsESPatternSigVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESPatternSigEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESPatternSigConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

def pottsESPatternClassCompatible (V : Finset (ℤ × ℤ)) {q : ℕ}
    (i : Fin q) (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (A : Configuration (pottsESGraph V)) : Prop :=
  (∀ x ∈ observed, x ∉ V → ξ x = i) ∧
  (∀ x ∈ pottsESObservedInteriorVertices V observed,
    ∀ y ∈ pottsESObservedInteriorVertices V observed,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x y →
        pottsESObservedGraphColor V i ξ x = pottsESObservedGraphColor V i ξ y) ∧
  (∀ x ∈ pottsESObservedInteriorVertices V observed,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x none →
        pottsESObservedGraphColor V i ξ x = i)

theorem pottsESObservedInteriorVertex_exists (V : Finset (ℤ × ℤ))
    (observed : Finset (ℤ × ℤ)) (v : PottsESVertex V)
    (hv : v ∈ pottsESObservedInteriorVertices V observed) :
    ∃ x, ∃ hxV : x ∈ V, x ∈ observed ∧
      pottsESInteriorVertex V x hxV = v := by
  classical
  rcases Finset.mem_image.mp hv with ⟨z, hz, hzv⟩
  have hzData := Finset.mem_filter.mp z.2
  exact ⟨z.1, hzData.2, hzData.1, by
    simpa [pottsESObservedInteriorVertices] using hzv⟩

theorem pottsESPatternColorings_nonempty_imp_classCompatible
    (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (A : Configuration (pottsESGraph V))
    (h : Nonempty (pottsESPatternColorings V i observed ξ A)) :
    pottsESPatternClassCompatible V i observed ξ A := by
  classical
  rcases h with ⟨σ⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hnot
    have hpat := σ.2.2 x hx
    have hEq : i = ξ x := by
      simpa [pottsExtend, hnot] using hpat
    exact hEq.symm
  · intro x hx y hy hxy
    obtain ⟨a, haV, haObs, hax⟩ :=
      pottsESObservedInteriorVertex_exists V observed x hx
    obtain ⟨b, hbV, hbObs, hby⟩ :=
      pottsESObservedInteriorVertex_exists V observed y hy
    have hspinX : pottsESSpin V i σ.1 x = ξ a := by
      have hpat := σ.2.2 a haObs
      rw [← hax]
      simpa [pottsESSpin, pottsESInteriorVertex, pottsExtend, haV] using hpat
    have hspinY : pottsESSpin V i σ.1 y = ξ b := by
      have hpat := σ.2.2 b hbObs
      rw [← hby]
      simpa [pottsESSpin, pottsESInteriorVertex, pottsExtend, hbV] using hpat
    have hcolorX : pottsESObservedGraphColor V i ξ x = ξ a := by
      rw [← hax]
      rfl
    have hcolorY : pottsESObservedGraphColor V i ξ y = ξ b := by
      rw [← hby]
      rfl
    have hconst :=
      (pottsESCompatible_iff_componentConst V i A σ.1).mp σ.2.1 hxy
    calc
      pottsESObservedGraphColor V i ξ x = pottsESSpin V i σ.1 x :=
        hcolorX.trans hspinX.symm
      _ = pottsESSpin V i σ.1 y := hconst
      _ = pottsESObservedGraphColor V i ξ y := hspinY.trans hcolorY.symm
  · intro x hx hxnone
    obtain ⟨a, haV, haObs, hax⟩ :=
      pottsESObservedInteriorVertex_exists V observed x hx
    have hspinX : pottsESSpin V i σ.1 x = ξ a := by
      have hpat := σ.2.2 a haObs
      rw [← hax]
      simpa [pottsESSpin, pottsESInteriorVertex, pottsExtend, haV] using hpat
    have hcolorX : pottsESObservedGraphColor V i ξ x = ξ a := by
      rw [← hax]
      rfl
    have hconst :=
      (pottsESCompatible_iff_componentConst V i A σ.1).mp σ.2.1 hxnone
    calc
      pottsESObservedGraphColor V i ξ x = pottsESSpin V i σ.1 x :=
        hcolorX.trans hspinX.symm
      _ = pottsESSpin V i σ.1 none := hconst
      _ = i := by simp [pottsESSpin]

theorem pottsESConnectivityPatternFunctional_eq_if_classCompatible
    (V : Finset (ℤ × ℤ)) {q : ℕ} (hq : 1 ≤ q) (i : Fin q)
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (A : Configuration (pottsESGraph V)) :
    pottsESConnectivityPatternFunctional V i observed ξ A =
      if _h : pottsESPatternClassCompatible V i observed ξ A then
        1 / (q : ℝ) ^ ((insert (Quotient.mk _ none)
          (pottsESObservedComponentClasses
            (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
            (pottsESObservedInteriorVertices V observed))).card - 1)
      else 0 := by
  classical
  by_cases h : pottsESPatternClassCompatible V i observed ξ A
  · rw [dite_eq_left h]
    rcases h with ⟨houtside, hstable, hghost⟩
    exact pottsESConnectivityPatternFunctional_eq_inv_pow
      V hq i observed ξ A houtside hstable hghost
  · rw [dite_eq_right h]
    have hempty : IsEmpty (pottsESPatternColorings V i observed ξ A) := by
      refine ⟨fun hs => ?_⟩
      exact h (pottsESPatternColorings_nonempty_imp_classCompatible
        V i observed ξ A ⟨hs⟩)
    have hzero : Nat.card (pottsESPatternColorings V i observed ξ A) = 0 :=
      Nat.card_of_isEmpty
    unfold pottsESConnectivityPatternFunctional
    rw [hzero]
    simp

theorem pottsESComponentRelation_iff_shellPairEvent
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x y : ℤ × ℤ) (hx : x ∈ pottsESSupport V) (hy : y ∈ pottsESSupport V)
    (hxV : x ∈ V) (hyV : y ∈ V) :
    (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r
        (some ⟨x, hx⟩) (some ⟨y, hy⟩) ↔
      pottsESShellBondExtension V A ∈ pottsESLatticePairRelationEvent V x y := by
  simpa [pottsESLatticePairRelationEvent, pottsESLatticeExitEventFrom] using
    (pottsESComponentRelation_iff_latticePathOrBothExit
      V A x y hx hy hxV hyV)

theorem pottsESComponentRelation_iff_shellExitAtGhost
    (V : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x : ℤ × ℤ) (hx : x ∈ pottsESSupport V) (hxV : x ∈ V) :
    (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r
        (some ⟨x, hx⟩) none ↔
      pottsESShellBondExtension V A ∈ pottsESLatticeExitEventFrom V x := by
  constructor
  · intro h
    have hparts := (pottsESComponentRelation_iff_pathOrBoundary V A
      (some ⟨x, hx⟩) none).mp h
    rcases hparts with hpath | ⟨hboundary, _⟩
    · exact False.elim (pottsESGraph_no_actual_path_to_ghost V A
        (some ⟨x, hx⟩) (by simp) hpath)
    · obtain ⟨b, hb, hxb⟩ := hboundary
      have hb' : b = none ∨ ∃ z, b = some z ∧ z.1 ∉ V := by
        simpa [pottsESBoundary] using hb
      rcases hb' with hbGhost | ⟨z, hbz, hzV⟩
      · subst b
        exact False.elim (pottsESGraph_no_actual_path_to_ghost V A
          (some ⟨x, hx⟩) (by simp) hxb)
      · subst b
        have hreach := (pottsESActualConnected_iff_latticeReachable
          V A x z.1 hx z.2).mp hxb
        exact ⟨z.1, hzV, hreach⟩
  · rintro ⟨z, hzV, hreach⟩
    have hne : x ≠ z := by
      intro hEq
      subst z
      exact hzV hxV
    have hzRC : z ∈
        (PD.rcInfiniteOpenGraph (pottsESShellBondExtension V A)).support :=
      SimpleGraph.mem_support_of_reachable hne.symm hreach.symm
    have hzSupport := pottsESSupport_of_rcInfiniteSupport V A hzRC
    have hpath := (pottsESActualConnected_iff_latticeReachable
      V A x z hx hzSupport).mpr hreach
    have hzBoundary : some ⟨z, hzSupport⟩ ∈ pottsESBoundary V := by
      rw [pottsESBoundary]
      exact Or.inr ⟨⟨z, hzSupport⟩, rfl, hzV⟩
    have hboundary := boundary_component (pottsESGraph V)
      (pottsESBoundaryCondition V) A
      ((BoundaryCondition.wired_rel (pottsESBoundary V)
        (some ⟨z, hzSupport⟩) none).2
        (Or.inr ⟨hzBoundary, by simp [pottsESBoundary]⟩))
    have hconnected := actualConnected_component (pottsESGraph V)
      (pottsESBoundaryCondition V) A hpath
    exact (componentSetoid (pottsESGraph V)
      (pottsESBoundaryCondition V) A).trans hconnected hboundary

end

end PottsContinuity.Thm1
