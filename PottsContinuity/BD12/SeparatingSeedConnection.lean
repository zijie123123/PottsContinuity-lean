module

public import PottsContinuity.BD12.SeedMediatedConnection
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! A path-separating seed set makes the seed-mediated observable exactly the
ordinary connection-to-target indicator, on every configuration. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
open scoped Classical
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance separatingEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance separatingEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Ordinary actual open connection from o to a finite target set. -/
def finiteConnectionToSetIndicator (o : V) (B : Finset V) (A : Configuration G) : ℝ :=
  if ∃ b, b ∈ B ∧ ActualConnected G A o b then 1 else 0

omit [Finite V] in
/-- A structural graph separator is sufficient for equality of the two literal
observables. The hypothesis concerns all original graph walks, independently
of the configuration or probability law. -/
theorem finiteConnectionToSetIndicator_eq_seedMediated_of_separator
    (S B : Finset V) (o : V)
    (hsep : ∀ b, b ∈ B → ∀ p : G.Walk o b, ∃ s, s ∈ p.support ∧ s ∈ S) :
    finiteConnectionToSetIndicator G o B = seedMediatedIndicator G S B o := by
  classical
  funext A
  have heq : (∃ b, b ∈ B ∧ ActualConnected G A o b) ↔ seedMediatedConnection G S B o A := by
    constructor
    · rintro ⟨b, hb, ⟨p⟩⟩
      obtain ⟨s, hsp, hsS⟩ := hsep b hb (p.mapLe (openGraph_le G A))
      have hs : s ∈ p.support := by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hsp
      exact ⟨s, hsS, b, hb, (p.takeUntil s hs).reachable.symm, (p.dropUntil s hs).reachable⟩
    · rintro ⟨s, _, b, hb, hso, hsb⟩
      exact ⟨b, hb, hso.symm.trans hsb⟩
  simp only [finiteConnectionToSetIndicator, seedMediatedIndicator, heq]

omit [Finite V] in
theorem finiteConnectionToSetIndicator_mem_Icc (o : V) (B : Finset V) (A : Configuration G) :
    finiteConnectionToSetIndicator G o B A ∈ Set.Icc (0 : ℝ) 1 := by
  unfold finiteConnectionToSetIndicator
  split_ifs <;> norm_num

omit [Finite V] in
theorem finiteConnectionToSetIndicator_monotone (o : V) (B : Finset V) :
    Monotone (finiteConnectionToSetIndicator G o B) := by
  classical
  intro A D hAD
  by_cases hA : ∃ b, b ∈ B ∧ ActualConnected G A o b
  · obtain ⟨b, hb, hob⟩ := hA
    have hD : ∃ b, b ∈ B ∧ ActualConnected G D o b := ⟨b, hb, actualConnected_mono hAD hob⟩
    have hA' : ∃ b, b ∈ B ∧ ActualConnected G A o b := ⟨b, hb, hob⟩
    simp only [finiteConnectionToSetIndicator, ite_eq_left hD, ite_eq_left hA', le_refl]
  · simp only [finiteConnectionToSetIndicator, ite_eq_right hA]
    split_ifs <;> norm_num

end
end PottsContinuity.BD12
