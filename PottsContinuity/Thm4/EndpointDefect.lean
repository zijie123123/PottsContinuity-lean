module

public import PottsContinuity.Thm4.ModifiedContourIdentity
public import PottsContinuity.Thm4.CriticalEdgeToggle

/-!
# The actual local winding defect at q = 4

This is the signed internal-port sum in one actual finite edge fiber, before
averaging over the FK law. Its weighted cancellation under edge toggling is proved
in `Thm4/WindingCancellation.lean` (`windingAtomicDefect_probability_pair_cancel_four`).
No exponential phase at complementary spin zero is substituted for the winding
observable.
-/

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial

noncomputable section

local instance endpointDefectPortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := Fintype.ofFinite _

/-- The actual internal port occurrences supported on a specified finite cover edge. -/
def windingEdgePorts (n : ℕ) (e : (ParafermionicAmbientGraph n).edgeSet) :
    Finset (ParafermionicCoverFinitePort n) := by
  classical
  exact Finset.univ.filter (fun c =>
    parafermionicCoverFinitePortOtherEndpointInBox n c ∧
      (parafermionicCoverPortEdge c.1).val = Sym2.map Subtype.val e.val)

/-- The local signed winding sum for one configuration and one internal edge.
The edge state is read from the actual finite configuration through its unique
exploration; the definition inserts no local cancellation relation. -/
def windingAtomicDefect (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (A : Configuration (ParafermionicAmbientGraph n)) : ℝ :=
  ∑ c ∈ windingEdgePorts n e,
    (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
      parafermionicCoverPathWindingAtom n hn A (c, true)

/-- If the actual exploration visits none of an edge's retained internal ports,
its winding defect is zero. This lemma does not identify the geometric event with an
edge-cut return class. -/
lemma windingAtomicDefect_eq_zero_of_no_visits (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (A : Configuration (ParafermionicAmbientGraph n))
    (hno : ∀ c ∈ windingEdgePorts n e,
      (c, true) ∉ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) :
    windingAtomicDefect n hn e A = 0 := by
  unfold windingAtomicDefect
  apply Finset.sum_eq_zero
  intro c hc
  simp only [parafermionicCoverPathWindingAtom, hno c hc, ↓reduceDIte, mul_zero]

end
end PottsContinuity.Thm4
