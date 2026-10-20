module

public import PottsContinuity.Thm3.Push.CompleteSourcePrefixSelector
public import PottsContinuity.Exploration.DependentPairPathDMP

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance completeSourcePrefixDMPEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _
local instance completeSourcePrefixDMPEdgeFintype (n : ℕ) :
    Fintype (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Fintype.ofFinite _
local instance completeSourcePrefixDMPRemainingFintype (n : ℕ)
    (R : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Fintype (RemainingConfiguration (rectangleGraph (0,0) (2*n) (2*n)) R) := Fintype.ofFinite _

/-- The actual all-height source tip, followed by a direct prefix or the
fully observed source-connection alternative. -/
def caseTwoCompleteSourceRevealMap (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n)))) :
    RevealMap (G := rectangleGraph (0,0) (2*n) (2*n)) :=
  dependentPairPathRevealMap (caseTwoTipEndpointSelector n s hfit)
    (caseTwoCompletePrefixSelector n s hfit selectPrefix)
    (caseTwoTipEndpointReveal n s hfit) (caseTwoCompletePrefixSecondReveal n s hfit)

/-- A successful direct-prefix branch observes exactly the two retained
augmented exteriors and slit bonds. It adds no discarded completion query. -/
theorem caseTwoCompleteSourceRevealMap_eq_of_prefix
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n)))
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hr : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some (.inl trace)) :
    caseTwoCompleteSourceRevealMap n s hfit selectPrefix C = caseTwoStoppedPrefixReveal n s hfit b trace := by
  have hy := ((caseTwoCompletePrefixSelector_eq_inl_iff n s hfit selectPrefix b C trace).mp hr).1
  simp only [caseTwoCompleteSourceRevealMap,dependentPairPathRevealMap,dependentPairPathSelector,
    hb,Option.bind_some,hr,Option.map_some,caseTwoTipEndpointReveal,ite_eq_left hy,caseTwoCompletePrefixSecondReveal]
  exact Finset.union_eq_right.mpr (caseTwoTipRightReveal_subset_stoppedPrefixReveal n s hfit b trace)

/-- The alternative source-connection branch has exactly the fully observed
geometry required by the source product consumer, with actual open walks. -/
theorem caseTwoCompleteSource_connection_branch_geometry
    (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hr : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some (.inr ())) :
    caseTwoCompleteSourceRevealMap n s hfit selectPrefix C = Finset.univ ∧
      ∃ a b t u : RectangleVertex (0,0) (2*n) (2*n),
      ∃ p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a t,
      ∃ q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk b u,
        a ∈ intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)) ∧
        b ∈ intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ)) ∧
        ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  constructor
  · simp only [caseTwoCompleteSourceRevealMap,dependentPairPathRevealMap,dependentPairPathSelector,
      hb,Option.bind_some,hr,Option.map_some,caseTwoCompletePrefixSecondReveal]
    exact Finset.union_eq_right.mpr (Finset.subset_univ (caseTwoTipEndpointReveal n s hfit b))
  · obtain ⟨a,ha,c,hc,⟨p⟩⟩ := caseTwoCompletePrefixSelector_inr_connects n s hfit selectPrefix b C hr
    exact ⟨a,c,c,c,p,.nil,ha,hc,c,p.end_mem_support,List.mem_singleton_self c⟩

/-- All first-stage and connection-branch locality is proved. Only direct
positive-prefix value locality remains an exploration interface. -/
theorem caseTwoCompleteSourceRevealMap_stable_of_prefixLocality
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (hprefix : ∀ C D b trace,
      caseTwoTipEndpointSelector n s hfit C = some b → 0 < b.2.val.2 →
      selectPrefix b C = some trace →
      D ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
        C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → selectPrefix b D = some trace) :
    ∀ C D, D ∩ caseTwoCompleteSourceRevealMap n s hfit selectPrefix C =
      C ∩ caseTwoCompleteSourceRevealMap n s hfit selectPrefix C →
      caseTwoCompleteSourceRevealMap n s hfit selectPrefix D =
        caseTwoCompleteSourceRevealMap n s hfit selectPrefix C := by
  exact dependentPairPathRevealMap_stable (caseTwoTipEndpointSelector n s hfit)
    (caseTwoCompletePrefixSelector n s hfit selectPrefix)
    (caseTwoTipEndpointReveal n s hfit) (caseTwoCompletePrefixSecondReveal n s hfit)
    (caseTwoTipEndpointSelector_oneSidedStable n s hs hfit)
    (caseTwoCompletePrefixSelector_stable_of_prefixLocality n s hfit selectPrefix hprefix)

end
end PottsContinuity.Push
