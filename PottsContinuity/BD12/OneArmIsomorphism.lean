module

public import PottsContinuity.BD12.RadiusOneArmComparison
public import PottsContinuity.PD.FK.Isomorphism
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! One-arm observables transported by an actual graph isomorphism preserving
the supplied integer radius functions. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
open scoped Classical

/-- Exact pointwise equality of the sampled 0/1 observables under relabelling. -/
theorem radiusOneArmIndicator_configurationIso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (r : V → ℕ) (s : W → ℕ)
    (hr : ∀ v, s (e v) = r v) (o : V) (n : ℕ) (A : Configuration G) :
    radiusOneArmIndicator H s (e o) n (configurationIso e A) = radiusOneArmIndicator G r o n A := by
  have hiff : (∃ b, s b = n ∧ FKC.FiniteFK.ActualConnected H (configurationIso e A) (e o) b) ↔
      (∃ b, r b = n ∧ FKC.FiniteFK.ActualConnected G A o b) := by
    constructor
    · rintro ⟨b, hb, hconn⟩
      obtain ⟨v, rfl⟩ := e.surjective b
      exact ⟨v, (hr v) ▸ hb, (actualConnected_configurationIso e A o v).mp hconn⟩
    · rintro ⟨b, hb, hconn⟩
      exact ⟨e b, (hr b).trans hb, (actualConnected_configurationIso e A o b).mpr hconn⟩
  simp only [radiusOneArmIndicator, finiteConnectionToSetIndicator, mem_finiteRadiusShell]
  by_cases hG : ∃ b, r b = n ∧ FKC.FiniteFK.ActualConnected G A o b
  · simp only [ite_eq_left hG]
    exact ite_eq_left (hiff.mpr hG)
  · simp only [ite_eq_right hG]
    exact ite_eq_right (fun hH => hG (hiff.mp hH))

end
end PottsContinuity.BD12
