module

public import PottsContinuity.Thm3.OuterCircuit.FiniteEnvelopeReveal

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Exploration

noncomputable section

theorem outerCircuitBoundaryEdge_mem_boolConfigurationEquiv_iff_rcAdj
    {n : ℕ} (ω : (lemma4AmbientGraph n).edgeSet → Bool)
    (i : OuterCircuitPolygonCode n) (j : ZMod (i.1.val + 3)) :
    outerCircuitBoundaryEdge i j ∈ boolConfigurationEquiv (lemma4AmbientGraph n) ω ↔
      (PottsContinuity.rcOpenGraph (box (56*n)) ω).Adj
        ⟨(outerCircuitCodePolygon i).vertex j,
          outerCircuitCodePolygon_vertex_mem i j⟩
        ⟨(outerCircuitCodePolygon i).vertex (j+1),
          outerCircuitCodePolygon_vertex_mem i (j+1)⟩ := by
  have hGraph : openGraph (lemma4AmbientGraph n)
      (boolConfigurationEquiv (lemma4AmbientGraph n) ω) =
        PottsContinuity.rcOpenGraph (box (56*n)) ω := by
    rw [openGraph_boolConfigurationEquiv]
    rfl
  have hval := outerCircuitBoundaryEdge_val i j
  calc
    outerCircuitBoundaryEdge i j ∈ boolConfigurationEquiv (lemma4AmbientGraph n) ω ↔
        (outerCircuitBoundaryEdge i j).val ∈
          openEdges (lemma4AmbientGraph n)
            (boolConfigurationEquiv (lemma4AmbientGraph n) ω) :=
      (coe_mem_openEdges_iff (lemma4AmbientGraph n)
        (boolConfigurationEquiv (lemma4AmbientGraph n) ω)
        (outerCircuitBoundaryEdge i j)).symm
    _ ↔ (openGraph (lemma4AmbientGraph n)
          (boolConfigurationEquiv (lemma4AmbientGraph n) ω)).Adj
          ⟨(outerCircuitCodePolygon i).vertex j,
            outerCircuitCodePolygon_vertex_mem i j⟩
          ⟨(outerCircuitCodePolygon i).vertex (j+1),
            outerCircuitCodePolygon_vertex_mem i (j+1)⟩ := by
      rw [openGraph_adj, hval]
    _ ↔ (PottsContinuity.rcOpenGraph (box (56*n)) ω).Adj
          ⟨(outerCircuitCodePolygon i).vertex j,
            outerCircuitCodePolygon_vertex_mem i j⟩
          ⟨(outerCircuitCodePolygon i).vertex (j+1),
            outerCircuitCodePolygon_vertex_mem i (j+1)⟩ := by
      rw [hGraph]

theorem outerCircuitCandidateValid_implies_boolAnnulusEvent {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (i : OuterCircuitPolygonCode n)
    (hvalid : outerCircuitCandidateValid C i) :
    (boolConfigurationEquiv (lemma4AmbientGraph n)).symm C ∈
      annulusCircuitEvent (box (56*n)) (0,0) (7*n) := by
  rcases hvalid with ⟨hcenter, hrad, hopen⟩
  let P := outerCircuitCodePolygon i
  refine ⟨i.1.val, P, hcenter, ?_, ?_⟩
  · intro j
    have hj := hrad j
    constructor
    · simpa [Prod.fst, Prod.snd, sub_zero, Nat.cast_mul,
        Nat.cast_ofNat] using hj.1
    · have hj' : max |(P.vertex j).1 - (0,0).1|
          |(P.vertex j).2 - (0,0).2| ≤ (14*n : ℤ) := by
        simpa [P, Prod.fst, Prod.snd, sub_zero, Nat.cast_mul,
          Nat.cast_ofNat] using hj.2
      have hj'' : max |(P.vertex j).1 - (0,0).1|
          |(P.vertex j).2 - (0,0).2| ≤ 2 * (7*(n : ℤ)) := by omega
      exact hj''
  · intro j
    refine ⟨outerCircuitCodePolygon_vertex_mem i j,
      outerCircuitCodePolygon_vertex_mem i (j+1), ?_⟩
    have hopenBool : outerCircuitBoundaryEdge i j ∈
        boolConfigurationEquiv (lemma4AmbientGraph n)
          ((boolConfigurationEquiv (lemma4AmbientGraph n)).symm C) := by
      simpa only [Equiv.apply_symm_apply] using hopen j
    exact (outerCircuitBoundaryEdge_mem_boolConfigurationEquiv_iff_rcAdj
      ((boolConfigurationEquiv (lemma4AmbientGraph n)).symm C) i j).mp hopenBool

theorem outerCircuitCandidateValid_exists_of_boolAnnulusEvent {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (hEvent : (boolConfigurationEquiv (lemma4AmbientGraph n)).symm C ∈
      annulusCircuitEvent (box (56*n)) (0,0) (7*n)) :
    ∃ i : OuterCircuitPolygonCode n, outerCircuitCandidateValid C i := by
  obtain ⟨m, P, hcenter, hrad, hopen⟩ := hEvent
  have hvertices : ∀ j : ZMod (m+3), P.vertex j ∈ box (56*n) := by
    intro j
    exact (hopen j).1
  let mFin : Fin (Fintype.card (OuterCircuitHostVertex n) + 1) :=
    ⟨m, outerCircuitPolygon_index_lt_host_card P hvertices⟩
  let i : OuterCircuitPolygonCode n := ⟨mFin, ⟨P, hvertices⟩⟩
  have hcodePolygon : outerCircuitCodePolygon i = P := rfl
  refine ⟨i, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hcodePolygon] using hcenter
  · intro j
    have hj := hrad j
    constructor
    · simpa [hcodePolygon, Prod.fst, Prod.snd, sub_zero,
        Nat.cast_mul, Nat.cast_ofNat] using hj.1
    · have hrad' : max |(P.vertex j).1| |(P.vertex j).2| ≤
          (14*n : ℤ) := by
        have hsrc := hj.2
        simp only [sub_zero] at hsrc
        omega
      simpa only [hcodePolygon] using hrad'
  · intro j
    obtain ⟨hj, hj', hadj⟩ := hopen j
    have hEdgeBool : outerCircuitBoundaryEdge i j ∈
        boolConfigurationEquiv (lemma4AmbientGraph n)
          ((boolConfigurationEquiv (lemma4AmbientGraph n)).symm C) :=
      (outerCircuitBoundaryEdge_mem_boolConfigurationEquiv_iff_rcAdj
        ((boolConfigurationEquiv (lemma4AmbientGraph n)).symm C) i j).mpr
          (by simpa only [hcodePolygon] using hadj)
    have hEq : boolConfigurationEquiv (lemma4AmbientGraph n)
        ((boolConfigurationEquiv (lemma4AmbientGraph n)).symm C) = C :=
      Equiv.apply_symm_apply (boolConfigurationEquiv (lemma4AmbientGraph n)) C
    simpa only [hEq] using hEdgeBool

theorem lemma4OuterAnnulusEvent_iff_candidate_exists {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    C ∈ lemma4OuterAnnulusEvent n ↔
      ∃ i : OuterCircuitPolygonCode n, outerCircuitCandidateValid C i := by
  change (boolConfigurationEquiv (lemma4AmbientGraph n)).symm C ∈
      annulusCircuitEvent (box (56*n)) (0,0) (7*n) ↔ _
  constructor
  · exact outerCircuitCandidateValid_exists_of_boolAnnulusEvent C
  · rintro ⟨i, hvalid⟩
    exact outerCircuitCandidateValid_implies_boolAnnulusEvent C i hvalid

end
end PottsContinuity.OuterCircuit
