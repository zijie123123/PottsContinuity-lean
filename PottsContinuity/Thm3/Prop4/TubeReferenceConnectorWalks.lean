module

public import PottsContinuity.Thm3.Prop4.TubeCentralRetainedBonds
public import PottsContinuity.Thm3.Prop4.TubeConnectorHeights
public import PottsContinuity.Thm3.Prop4.RectangleDeletedReferenceGraph

/-!
# Genuine sampled vertical connectors of the tube reference

Each step crosses an original physical horizontal bond outside the revealed
cut interval. The connectors include their actual root, exact length and
support interval; they stop at the physical exterior before leaving it.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

private theorem vertical_graph_walk_nat (H : SimpleGraph LatticeVertex) (a : ℤ) (m : ℕ)
    (hc : ∀ y : ℤ, a < y → y ≤ a+(m : ℤ) → H.Adj (0,y-1) (0,y)) :
    ∃ p : H.Walk (0,a) (0,a+(m : ℤ)), p.length = m ∧
      ∀ z ∈ p.support, z.1 = 0 ∧ a ≤ z.2 ∧ z.2 ≤ a+(m : ℤ) := by
  induction m with
  | zero =>
    refine ⟨(.nil : H.Walk (0,a) (0,a)).copy rfl (by simp),by simp,?_⟩
    intro z hz
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
    rw [hz]
    simp
  | succ m ih =>
    obtain ⟨p,hplen,hp⟩ := ih (fun y hya hyb => hc y hya (by omega))
    have hh := hc (a+((m+1 : ℕ) : ℤ)) (by omega) le_rfl
    have hstep : H.Adj (0,a+(m : ℤ)) (0,a+((m+1 : ℕ) : ℤ)) := by
      convert hh using 1; congr 1; omega
    refine ⟨p.concat hstep,by simp only [SimpleGraph.Walk.length_concat,hplen],?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | rfl
    · have hh := hp z hz
      exact ⟨hh.1,hh.2.1,by omega⟩
    · exact ⟨rfl,by omega,le_rfl⟩

/-- Consecutive actual row steps give a vertical walk with exact length and support. -/
theorem vertical_graph_walk_of_row_steps (H : SimpleGraph LatticeVertex)
    (a b : ℤ) (hab : a ≤ b)
    (hc : ∀ y : ℤ, a < y → y ≤ b → H.Adj (0,y-1) (0,y)) :
    ∃ p : H.Walk (0,a) (0,b), p.length = (b-a).toNat ∧
      ∀ z ∈ p.support, z.1=0 ∧ a ≤ z.2 ∧ z.2 ≤ b := by
  let m := (b-a).toNat
  have hm : a+(m : ℤ) = b := by
    dsimp [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  obtain ⟨p,hplen,hp⟩ := vertical_graph_walk_nat H a m
    (fun y hya hyb => hc y hya (by omega))
  refine ⟨p.copy rfl (by rw [hm]),by simpa only [SimpleGraph.Walk.length_copy] using hplen,?_⟩
  rw [SimpleGraph.Walk.support_copy]
  intro z hz
  have hh := hp z hz
  exact ⟨hh.1,hh.2.1,by omega⟩

end
end PottsContinuity.Thm3.Prop4
