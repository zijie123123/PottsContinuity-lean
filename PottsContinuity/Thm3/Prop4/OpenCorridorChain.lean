module

public import PottsContinuity.Thm3.Prop4.OpenCorridorGluing
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Finite chains of actual corridor crossings

Each horizontal walk remains unchanged. Consecutive vertical overlap walks
connect their initial vertices inside D. The final concatenation therefore
retains D even when the accumulated path leaves every single horizontal band.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- A finite chain with actual overlap connectors yields one actual walk entirely inside D. -/
theorem original_open_corridor_chain (ω : LatticeConfiguration) (D : Set LatticeVertex)
    (K : ℕ) (hK : 1 ≤ K) (s : ℕ) (X Y : ℕ → ℤ)
    (u v : Fin K → LatticeVertex)
    (p : ∀ i : Fin K, (PD.rcInfiniteOpenGraph ω).Walk (u i) (v i))
    (hu : ∀ i, (u i).1 = X i.val) (hv : ∀ i, (v i).1 = X i.val+2*(s : ℤ))
    (hband : ∀ i z, z ∈ (p i).support → Y i.val-(s : ℤ) ≤ z.2 ∧ z.2 ≤ Y i.val+(s : ℤ))
    (hD : ∀ i z, z ∈ (p i).support → z ∈ D)
    (hstep : ∀ i : ℕ, i+1 < K → 0 ≤ X (i+1)-X i ∧ X (i+1)-X i ≤ (s : ℤ))
    (hlink : ∀ i : ℕ, i+1 < K → ∃ a b : LatticeVertex,
      ∃ V : (PD.rcInfiniteOpenGraph ω).Walk a b,
        a.2 = min (Y i) (Y (i+1))-(s : ℤ) ∧ b.2 = max (Y i) (Y (i+1))+(s : ℤ) ∧
        (∀ z ∈ V.support, X (i+1) ≤ z.1 ∧ z.1 ≤ X (i+1)+(s : ℤ) ∧
          min (Y i) (Y (i+1))-(s : ℤ) ≤ z.2 ∧ z.2 ≤ max (Y i) (Y (i+1))+(s : ℤ)) ∧
        (∀ z ∈ V.support, z ∈ D)) :
    ∃ W : (PD.rcInfiniteOpenGraph ω).Walk (u ⟨0,by omega⟩) (v ⟨K-1,by omega⟩),
      ∀ z ∈ W.support, z ∈ D := by
  have hreach : ∀ k : ℕ, ∀ hk : k < K,
      ∃ R : (PD.rcInfiniteOpenGraph ω).Walk (u ⟨0,by omega⟩) (u ⟨k,hk⟩),
        ∀ z ∈ R.support, z ∈ D := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨.nil,?_⟩
      intro z hz
      have hz' : z = u ⟨0,hk⟩ := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
      subst z
      exact hD ⟨0,hk⟩ _ (p ⟨0,hk⟩).start_mem_support
    | succ k ih =>
      intro hk
      obtain ⟨R,hR⟩ := ih (by omega)
      obtain ⟨a,b,V,ha,hb,hVB,hVD⟩ := hlink k hk
      have hx := hstep k hk
      let ip : Fin K := ⟨k,by omega⟩
      let ic : Fin K := ⟨k+1,hk⟩
      have hup := hu ip
      have hvp := hv ip
      have huc := hu ic
      have hvc := hv ic
      change (u ip).1 = X k at hup
      change (v ip).1 = X k+2*(s : ℤ) at hvp
      change (u ic).1 = X (k+1) at huc
      change (v ic).1 = X (k+1)+2*(s : ℤ) at hvc
      have hbt : min (Y k) (Y (k+1))-(s : ℤ) ≤ max (Y k) (Y (k+1))+(s : ℤ) := by
        have hmin : min (Y k) (Y (k+1)) ≤ max (Y k) (Y (k+1)) := min_le_max
        omega
      obtain ⟨C,hC⟩ := original_open_corridor_connector ω D
        (X (k+1)) (X (k+1)+(s : ℤ))
        (min (Y k) (Y (k+1))-(s : ℤ)) (max (Y k) (Y (k+1))+(s : ℤ))
        (by omega) hbt (p ip) (p ic) V (by omega) (by omega) (by omega) (by omega)
        (by
          intro z hz
          have hh := hband ip z hz
          change Y k-(s : ℤ) ≤ z.2 ∧ z.2 ≤ Y k+(s : ℤ) at hh
          omega)
        (by
          intro z hz
          have hh := hband ic z hz
          change Y (k+1)-(s : ℤ) ≤ z.2 ∧ z.2 ≤ Y (k+1)+(s : ℤ) at hh
          omega)
        hVB ha hb (hD ip) (hD ic) hVD
      refine ⟨R.append C,?_⟩
      intro z hz
      rcases (SimpleGraph.Walk.mem_support_append_iff R C).mp hz with hz | hz
      · exact hR z hz
      · exact hC z hz
  obtain ⟨R,hR⟩ := hreach (K-1) (by omega)
  refine ⟨R.append (p ⟨K-1,by omega⟩),?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact hR z hz
  · exact hD _ z hz

end
end PottsContinuity.Thm3.Prop4
