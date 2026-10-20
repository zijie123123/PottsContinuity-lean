module

public import PottsContinuity.PlanarMixed.Lemma4Connectors.SourceTraceStrip

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.Duality RSW MeasureTheory
noncomputable section

/-- Primal between-trace vertices defined by the full closed trace loop. -/
def traceIndexRegion (V : Finset LatticeVertex) {s : LatticeVertex}
    (P : PD.FK.squareLattice.Walk s s) : Set (V : Set LatticeVertex) :=
  {v | rayIndex v.val P = 1}

/-- The full trace index region supplies the exact strip/Omega premise of
the primal window clipping theorem, including all vertices of both cores. -/
theorem lemma4_strip_in_traceIndexRegion
    (n : ℕ) (A : Configuration (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)))
    {s : LatticeVertex} (P : PD.FK.squareLattice.Walk s s)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hsupport : ∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2 ∧ v.2 ≤ 3*(n:ℤ)-1)
    (hcore : ∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set LatticeVertex),
      ∀ u ∈ vertexBoxRegion (box (56*n)) z (2*n), rayIndex u.val P = 1) :
    ∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set LatticeVertex),
      ∀ u ∈ vertexBoxRegion (box (56*n)) z (2*n), ∀ w, ActualConnected _ A u w →
        w ∈ traceIndexRegion (box (56*n)) P ∧
        -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ) := by
  intro z hz u hu w huw
  have hui := hcore z hz u hu
  have hstrip := closedTraceLoop_component_strip (box (56*n)) A P hclosed
    (-3*(n:ℤ)) (3*(n:ℤ)-1) hsupport (by rw [hui]; norm_num) huw
  have heq := rayIndex_eq_of_avoidance_reachable P
    (huw.map (finiteDualScreenOpenHom (box (56*n)) A P hclosed))
  change rayIndex u.val P = rayIndex w.val P at heq
  exact ⟨heq.symm.trans hui,hstrip.2.1,by omega⟩

/-- All corrected primal noncrossings and the actual full trace loop give
whole-core confinement in the original radius-eight reference boxes. -/
theorem lemma4_confined_boxes_of_traceIndex_noncrossings
    (n : ℕ) (A : Configuration (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)))
    {s : LatticeVertex} (P : PD.FK.squareLattice.Walk s s)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hsupport : ∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2 ∧ v.2 ≤ 3*(n:ℤ)-1)
    (hcore : ∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set LatticeVertex),
      ∀ u ∈ vertexBoxRegion (box (56*n)) z (2*n), rayIndex u.val P = 1)
    (hconnectors : A ∈ lemma4PrimalNoncrossings (box (56*n)) (traceIndexRegion (box (56*n)) P) n) :
    A ∈ fullCoreConfined (box (56*n))
      (finiteVertexRegion (latticeBox (-5*(n:ℤ),0) (8*n)) (box (56*n))) (-5*(n:ℤ),0) n ∧
    A ∈ fullCoreConfined (box (56*n))
      (finiteVertexRegion (latticeBox (5*(n:ℤ),0) (8*n)) (box (56*n))) (5*(n:ℤ),0) n :=
  lemma4_confined_boxes_of_noncrossings_and_strip (box (56*n)) (traceIndexRegion (box (56*n)) P) n A
    (lemma4_strip_in_traceIndexRegion n A P hclosed hsupport hcore) hconnectors

/-- The repaired trace event records only original closed bonds, full-core
indices and the three literal decreasing primal noncrossings. -/
def lemma4TraceNoncrossingAnnulusEvent (n : ℕ) :
    Set (Configuration (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex))) :=
  {A | A ∈ finiteBoolEvent (box (56*n)) (fun ω => ω ∈ annulusCircuitEvent (box (56*n)) (-5*(n:ℤ),0) n) ∧
    A ∈ finiteBoolEvent (box (56*n)) (fun ω => ω ∈ annulusCircuitEvent (box (56*n)) (5*(n:ℤ),0) n) ∧
    ∃ s : LatticeVertex, ∃ P : PD.FK.squareLattice.Walk s s,
      finiteDualWalkClosed (box (56*n)) A P ∧
      (∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2 ∧ v.2 ≤ 3*(n:ℤ)-1) ∧
      (∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set LatticeVertex),
        ∀ u ∈ vertexBoxRegion (box (56*n)) z (2*n), rayIndex u.val P = 1) ∧
      A ∈ lemma4PrimalNoncrossings (box (56*n)) (traceIndexRegion (box (56*n)) P) n}

/-- The complete upper-product estimate for the literal repaired primal
trace event. No selected random domain or probability premise is assumed. -/
theorem lemma4_trace_noncrossing_annulus_probability_le_square (θ : Parameters) (n : ℕ) :
    (measure (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)) θ (BoundaryCondition.free ∅)
      (lemma4TraceNoncrossingAnnulusEvent n)).toReal ≤ (annulusProbability θ 8 n)^2 := by
  refine (measureReal_mono ?_).trans (lemma4_confined_annulus_pair_probability_le_square θ n)
  rintro A ⟨ha,hb,s,P,hclosed,hsupport,hcore,hconnectors⟩
  have h := lemma4_confined_boxes_of_traceIndex_noncrossings n A P hclosed hsupport hcore hconnectors
  exact ⟨ha,hb,h⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
