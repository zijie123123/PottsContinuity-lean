module

public import PottsContinuity.PlanarMixed.Lemma4Connectors.GlobalTraceLoop
public import PottsContinuity.PlanarMixed.Lemma4Connectors.SourceConfinement

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality RSW PlanarTopology
noncomputable section

/-- The original closed lower and upper crossings confine both entire cores
to the strict source strip, retaining their full traces, including every fold. -/
theorem lemma4_closed_trace_pair_core_strip
    (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)))
    (a b c d : ℤ)
    (p : PD.FK.squareLattice.Walk (-56*(n:ℤ)-1,a) (56*(n:ℤ),b))
    (q : PD.FK.squareLattice.Walk (56*(n:ℤ),c) (-56*(n:ℤ)-1,d))
    (hp : ∀ z ∈ p.support, -3*(n:ℤ) ≤ z.2 ∧ z.2 < -2*(n:ℤ))
    (hq : ∀ z ∈ q.support, 2*(n:ℤ) ≤ z.2 ∧ z.2 ≤ 3*(n:ℤ)-1)
    (hpclosed : ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ p.edges →
      ∀ e : (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)).edgeSet,
        Sym2.map Subtype.val e.val = b.toSym2 → e ∉ A)
    (hqclosed : ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ q.edges →
      ∀ e : (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)).edgeSet,
        Sym2.map Subtype.val e.val = b.toSym2 → e ∉ A) :
    ∃ P : PD.FK.squareLattice.Walk (-56*(n:ℤ)-1,a) (-56*(n:ℤ)-1,a),
      finiteDualWalkClosed (box (56*n)) A P ∧
      (∀ z ∈ P.support, -3*(n:ℤ) ≤ z.2 ∧ z.2 ≤ 3*(n:ℤ)-1) ∧
      (∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set LatticeVertex),
        ∀ u ∈ vertexBoxRegion (box (56*n)) z (2*n), ∀ w,
        ActualConnected _ A u w →
          rayIndex w.val P = 1 ∧ -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ)) := by
  obtain ⟨P,hsupport,hallowed,hindex⟩ := exists_betweenTraceLoop
    (-56*(n:ℤ)-1) (56*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)-1)
    (-2*(n:ℤ)) (2*(n:ℤ)) (by omega) a b c d p q hp hq
  have hV : ∀ v ∈ box (56*n), -56*(n:ℤ)-1 < v.1 ∧ v.1 ≤ 56*(n:ℤ) := by
    intro v hv
    rw [Foundations.mem_box_iff_interval] at hv
    push_cast at hv
    omega
  have hclosed := betweenTraceLoop_closed (box (56*n)) A
    (-56*(n:ℤ)-1) (56*(n:ℤ)) hV p q P hallowed hpclosed hqclosed
  refine ⟨P,hclosed,hsupport,?_⟩
  intro z hz u hu w huw
  have huindex : rayIndex u.val P = 1 := by
    change max |u.val.1-z.1| |u.val.2-z.2| ≤ ((2*n:ℕ):ℤ) at hu
    have hx := (abs_le.mp ((le_max_left _ _).trans hu))
    have hy := (abs_le.mp ((le_max_right _ _).trans hu))
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hx hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    all_goals
      apply hindex <;> dsimp at hx hy ⊢ <;> omega
  have hstrip := closedTraceLoop_component_strip (box (56*n)) A P hclosed
    (-3*(n:ℤ)) (3*(n:ℤ)-1) hsupport (by rw [huindex]; norm_num) huw
  have heq := rayIndex_eq_of_avoidance_reachable P
    (huw.map (finiteDualScreenOpenHom (box (56*n)) A P hclosed))
  change rayIndex u.val P = rayIndex w.val P at heq
  exact ⟨heq.symm.trans huindex,hstrip.2.1,by omega⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
