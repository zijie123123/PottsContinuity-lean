module

public import PottsContinuity.Thm3.RSW.OpenCycleAnnulus
public import PottsContinuity.Thm3.RSW.FourStripSimpleCycle
public import PottsContinuity.Thm3.RSW.RayIndexBoxBounds
public import PottsContinuity.FKC.FiniteFK.SupportedWalkSplicing

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section

/-- Four actual sampled open paths with successive intersections and annular
support yield an actual simple circuit enclosing the center in its Jordan domain. -/
theorem annulusCircuitEvent_of_fourIntersectingOpenWalks
    (V : Finset LatticeVertex)
    (ω : (PottsContinuity.squareLattice.induce (V : Set LatticeVertex)).edgeSet → Bool)
    (c : LatticeVertex) (n : ℕ)
    {uT vT uR vR uB vB uL vL : (V : Set LatticeVertex)}
    (pT : (rcOpenGraph V ω).Walk uT vT) (pR : (rcOpenGraph V ω).Walk uR vR)
    (pB : (rcOpenGraph V ω).Walk uB vB) (pL : (rcOpenGraph V ω).Walk uL vL)
    (hTR : ∃ z, z ∈ pT.support ∧ z ∈ pR.support)
    (hRB : ∃ z, z ∈ pR.support ∧ z ∈ pB.support)
    (hBL : ∃ z, z ∈ pB.support ∧ z ∈ pL.support)
    (hLT : ∃ z, z ∈ pL.support ∧ z ∈ pT.support)
    (hT : ∀ v ∈ pT.support, (n:ℤ) < v.val.2-c.2)
    (hR : ∀ v ∈ pR.support, (n:ℤ) < v.val.1-c.1)
    (hB : ∀ v ∈ pB.support, (n:ℤ) < c.2-v.val.2)
    (hL : ∀ v ∈ pL.support, (n:ℤ) < c.1-v.val.1)
    (houter : ∀ v, (v ∈ pT.support ∨ v ∈ pR.support ∨
      v ∈ pB.support ∨ v ∈ pL.support) →
      max |v.val.1-c.1| |v.val.2-c.2| ≤ 2*(n:ℤ)) :
    ω ∈ annulusCircuitEvent V c n := by
  classical
  obtain ⟨a,haT,haR⟩ := hTR
  obtain ⟨b,hbR,hbB⟩ := hRB
  obtain ⟨d,hdB,hdL⟩ := hBL
  obtain ⟨e,heL,heT⟩ := hLT
  obtain ⟨qT,hqT⟩ := FKC.FiniteFK.walk_between_support pT heT haT
  obtain ⟨qR,hqR⟩ := FKC.FiniteFK.walk_between_support pR haR hbR
  obtain ⟨qB,hqB⟩ := FKC.FiniteFK.walk_between_support pB hbB hdB
  obtain ⟨qL,hqL⟩ := FKC.FiniteFK.walk_between_support pL hdL heL
  let φ := Thm3.Easy.p5ClosedWalkToSquareLattice V ω
  obtain ⟨z,q,hq,hi,hqe⟩ := four_supported_walks_simple_cycle φ c qT qR qB qL
    (fun v hv => by change c.2 ≤ v.val.2; have := hT v (hqT hv); omega)
    (fun v hv => by change c.1 ≤ v.val.1; have := hR v (hqR hv); omega)
    (fun v hv => by change v.val.2 < c.2; have := hB v (hqB hv); omega)
    (fun v hv => by change v.val.1 < c.1; have := hL v (hqL hv); omega)
  have hqs := cycle_support_subset_of_edges_subset
    ((qT.append qR).append (qB.append qL)) q hq hqe
  apply annulusCircuitEvent_of_openCycle_rayIndex V ω c n q hq hi
  intro v hv
  have hvp := hqs hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hvp
  have hx := le_max_left |v.val.1-c.1| |v.val.2-c.2|
  have hy := le_max_right |v.val.1-c.1| |v.val.2-c.2|
  have hxa := le_abs_self (v.val.1-c.1)
  have hya := le_abs_self (v.val.2-c.2)
  have hxn := neg_le_abs (v.val.1-c.1)
  have hyn := neg_le_abs (v.val.2-c.2)
  rcases hvp with (hv | hv) | (hv | hv)
  · exact ⟨by have := hT v (hqT hv); omega, houter v (Or.inl (hqT hv))⟩
  · exact ⟨by have := hR v (hqR hv); omega, houter v (Or.inr (Or.inl (hqR hv)))⟩
  · exact ⟨by have := hB v (hqB hv); omega,
      houter v (Or.inr (Or.inr (Or.inl (hqB hv))))⟩
  · exact ⟨by have := hL v (hqL hv); omega,
      houter v (Or.inr (Or.inr (Or.inr (hqL hv))))⟩

end
end PottsContinuity.RSW
