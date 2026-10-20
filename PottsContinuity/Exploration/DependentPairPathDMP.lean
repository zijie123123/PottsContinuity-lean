module

public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! A sequential pair record can retain a second path chosen from the first
record. This is useful when an endpoint of the second record is read from the
first path. -/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable section

local instance dependentPairPathEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance dependentPairPathEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance dependentPairPathRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- The dependent record retains the first path and then the second path
selected using that first path. -/
def dependentPairPathSelector {β γ : Type*}
    (first : Configuration G → Option β)
    (second : β → Configuration G → Option γ)
    (C : Configuration G) : Option (β × γ) :=
  (first C).bind fun b => (second b C).map fun c => (b, c)

/-- Reveal both path records. A missing record exposes the full finite sample. -/
def dependentPairPathRevealMap {β γ : Type*}
    (first : Configuration G → Option β)
    (second : β → Configuration G → Option γ)
    (revealFirst : β → Configuration G)
    (revealSecond : β → γ → Configuration G)
    (C : Configuration G) : Configuration G :=
  match dependentPairPathSelector first second C with
  | none => Finset.univ
  | some (b, c) => revealFirst b ∪ revealSecond b c

private theorem inter_left_of_union_inter_eq {α : Type*} [DecidableEq α]
    (A B R S : Finset α)
    (h : B ∩ (R ∪ S) = A ∩ (R ∪ S)) : B ∩ R = A ∩ R := by
  apply Finset.ext
  intro e
  have he := congrArg (fun T : Finset α => e ∈ T) h
  simp only [Finset.mem_inter, Finset.mem_union] at he ⊢
  constructor
  · rintro ⟨heB, heR⟩
    have hmem := he.mp ⟨heB, Or.inl heR⟩
    exact ⟨hmem.1, heR⟩
  · rintro ⟨heA, heR⟩
    have hmem := he.mpr ⟨heA, Or.inl heR⟩
    exact ⟨hmem.1, heR⟩

private theorem inter_right_of_union_inter_eq {α : Type*} [DecidableEq α]
    (A B R S : Finset α)
    (h : B ∩ (R ∪ S) = A ∩ (R ∪ S)) : B ∩ S = A ∩ S := by
  apply Finset.ext
  intro e
  have he := congrArg (fun T : Finset α => e ∈ T) h
  simp only [Finset.mem_inter, Finset.mem_union] at he ⊢
  constructor
  · rintro ⟨heB, heS⟩
    have hmem := he.mp ⟨heB, Or.inr heS⟩
    exact ⟨hmem.1, heS⟩
  · rintro ⟨heA, heS⟩
    have hmem := he.mpr ⟨heA, Or.inr heS⟩
    exact ⟨hmem.1, heS⟩

/-- Separate stability of the first selector and of the second selector after
the first record has been fixed makes the dependent pair reveal stable. -/
theorem dependentPairPathRevealMap_stable {β γ : Type*}
    (first : Configuration G → Option β)
    (second : β → Configuration G → Option γ)
    (revealFirst : β → Configuration G)
    (revealSecond : β → γ → Configuration G)
    (hFirst : ∀ C C' b, first C = some b →
      C' ∩ revealFirst b = C ∩ revealFirst b → first C' = some b)
    (hSecond : ∀ C C' b c, first C = some b → second b C = some c →
      C' ∩ revealSecond b c = C ∩ revealSecond b c → second b C' = some c) :
    ∀ C C', C' ∩ dependentPairPathRevealMap first second revealFirst revealSecond C =
      C ∩ dependentPairPathRevealMap first second revealFirst revealSecond C →
        dependentPairPathRevealMap first second revealFirst revealSecond C' =
          dependentPairPathRevealMap first second revealFirst revealSecond C := by
  intro C C' hagree
  classical
  cases hf : first C with
  | none =>
      simp [dependentPairPathRevealMap, dependentPairPathSelector, hf,
        Finset.inter_univ] at hagree
      subst C'
      rfl
  | some b =>
      cases hs : second b C with
      | none =>
          simp [dependentPairPathRevealMap, dependentPairPathSelector, hf, hs,
            Finset.inter_univ] at hagree
          subst C'
          rfl
      | some c =>
          have hfirstStates : C' ∩ revealFirst b = C ∩ revealFirst b := by
            exact inter_left_of_union_inter_eq C C' (revealFirst b)
              (revealSecond b c) (by simpa [dependentPairPathRevealMap,
                dependentPairPathSelector, hf, hs] using hagree)
          have hsecondStates : C' ∩ revealSecond b c = C ∩ revealSecond b c := by
            exact inter_right_of_union_inter_eq C C' (revealFirst b)
              (revealSecond b c) (by simpa [dependentPairPathRevealMap,
                dependentPairPathSelector, hf, hs] using hagree)
          have hf' : first C' = some b := hFirst C C' b hf hfirstStates
          have hs' : second b C' = some c := hSecond C C' b c hf hs hsecondStates
          simp [dependentPairPathRevealMap, dependentPairPathSelector, hf, hs, hf', hs']

end
end PottsContinuity.Exploration
