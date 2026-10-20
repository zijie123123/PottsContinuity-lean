-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverEq24RootCoreComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRectangleDualComparison
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreConnectivityLaw
public import PottsContinuity.FKC.FiniteFK.AdjacentBoundaryConnectionLowerBound
public import PottsContinuity.FKC.FiniteFK.RectangleFlowDimension

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance eq24CompareDualEdgeFintype (n : ℕ) :
    Fintype (rectangleDualBottomCollarInnerGraph n).edgeSet := Fintype.ofFinite _
local instance eq24CompareDualEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleDualBottomCollarInnerGraph n).edgeSet := Classical.decEq _
local instance eq24CompareDualCfgFintype (n : ℕ) :
    Fintype (Configuration (rectangleDualBottomCollarInnerGraph n)) := Fintype.ofFinite _
local instance eq24CompareCoreCfgFintype (n : ℕ) :
    Fintype (Configuration (generalRectangleDualBottomCoreGraph (-(n:ℤ),0) (2*n) n)) :=
  Fintype.ofFinite _
local instance eq24CompareAmbientCfgFintype (n : ℕ) :
    Fintype (Configuration (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n)) :=
  Fintype.ofFinite _

 theorem eq24OrdinaryOrigin_mem (n : ℕ) :
    (0,0) ∈ latticeRectangle (-(n:ℤ)-1,0) (2*n+1) n := by
  rw [mem_latticeRectangle]
  constructor <;> constructor <;> omega

/-- The literal origin in the ordinary rectangle corresponding to the retained
true-dual core. -/
def parafermionicCoverEq24OrdinaryOriginVertex (n : ℕ) :
    RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n :=
  ⟨(0,0), eq24OrdinaryOrigin_mem n⟩

/-- The ordinary, fully left/right/top-wired origin event used on the right
of the Eq. 24 root comparison. -/
def parafermionicCoverEq24OrdinaryOriginEvent (n : ℕ) :
    Set (Configuration (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n)) :=
  {A | ∃ z : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n,
    z ∈ generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n ∧
    ActualConnected (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) A
      (parafermionicCoverEq24OrdinaryOriginVertex n) z}

 theorem eq24DualVertex_mem (n : ℕ) (x y : ℤ) (hnx : -(n:ℤ)-1 ≤ x)
    (hpx : x ≤ n) (hny : -1 ≤ y) (hpy : y ≤ n) :
    (x,y) ∈ rectangleDualExpanded (-(n:ℤ),0) (2*n) n := by
  change (x,y) ∈ latticeRectangle (-(n:ℤ)-1,-1) (2*n+1) (n+1)
  rw [mem_latticeRectangle]
  constructor <;> constructor <;> omega

def parafermionicCoverEq24DualOriginVertex (n : ℕ) : rectangleDualBottomCollarInnerVertex n :=
  ⟨(0,0), eq24DualVertex_mem n 0 0 (by omega) (by omega) (by omega) (by omega)⟩

/-- Actual connection from the literal origin face base to the true three
dual sides; the lower face-base row is not wired. -/
def parafermionicCoverEq24DualOriginEvent (n : ℕ) :
    Set (Configuration (rectangleDualBottomCollarInnerGraph n)) :=
  {D | ∃ z ∈ rectangleDualBottomCollarInnerThreeSides n,
    ActualConnected (rectangleDualBottomCollarInnerGraph n) D
      (parafermionicCoverEq24DualOriginVertex n) z}

def eq24CoreOrigin (n : ℕ) :
    generalRectangleDualBottomCoreVertex (-(n:ℤ),0) (2*n) n :=
  ⟨parafermionicCoverEq24DualOriginVertex n,
    by norm_num [parafermionicCoverEq24DualOriginVertex]⟩

private theorem eq24OrdinaryCoreOrigin_eq (n : ℕ) :
    generalRectangleDualBottomCoreVertexEquiv (-(n:ℤ),0) (2*n) n (eq24CoreOrigin n) =
      parafermionicCoverEq24OrdinaryOriginVertex n := by
  apply Subtype.ext
  rfl

private theorem eq24CoreInclusionOrigin_eq (n : ℕ) :
    generalRectangleDualBottomCoreInclusion (-(n:ℤ),0) (2*n) n (eq24CoreOrigin n) =
      parafermionicCoverEq24DualOriginVertex n := by
  apply Subtype.ext
  rfl

theorem parafermionicCoverEq24OrdinaryOriginEvent_probability_eq_dualOriginEvent
    (n : ℕ) (q : ClusterWeight) :
    (measure (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) q
      (BoundaryCondition.wired
        (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n))
      (parafermionicCoverEq24OrdinaryOriginEvent n)).toReal =
    (measure (rectangleDualBottomCollarInnerGraph n) q
      (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n))
      (parafermionicCoverEq24DualOriginEvent n)).toReal := by
  let c := eq24CoreOrigin n
  have h := generalRectangleDualBottomCore_threeSideConnectivity_probability_eq
    (-(n:ℤ),0) (2*n) n q ({c} : Set _)
  have hleft : generalRectangleDualBottomCoreAmbientSeedBoundaryEvent
      (-(n:ℤ),0) (2*n) n ({c} : Set _) =
      parafermionicCoverEq24OrdinaryOriginEvent n := by
    ext A
    constructor
    · rintro ⟨u, hu, z, hz, hconn⟩
      simp only [Set.mem_singleton_iff] at hu
      subst u
      have hz' : z ∈ generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n := hz
      refine ⟨z, hz', ?_⟩
      rw [← eq24OrdinaryCoreOrigin_eq n]
      exact hconn
    · rintro ⟨z, hz, hconn⟩
      refine ⟨c, Set.mem_singleton c, z, hz, ?_⟩
      rw [eq24OrdinaryCoreOrigin_eq n]
      exact hconn
  have hright : generalRectangleDualBottomCoreTrueDualSeedBoundaryEvent
      (-(n:ℤ),0) (2*n) n ({c} : Set _) =
      parafermionicCoverEq24DualOriginEvent n := by
    ext D
    constructor
    · rintro ⟨u, hu, z, hz, hconn⟩
      simp only [Set.mem_singleton_iff] at hu
      subst u
      have hz' : z ∈ rectangleDualBottomCollarInnerThreeSides n := by
        simp only [generalRectangleDualBottomCollarInnerThreeSides,
          rectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq] at hz ⊢
        rcases hz with hleft | hright | htop <;> omega
      refine ⟨z, hz', ?_⟩
      change ActualConnected (rectangleDualGraph (-(n:ℤ),0) (2*n) n) D
        (generalRectangleDualBottomCoreInclusion (-(n:ℤ),0) (2*n) n c) z at hconn
      rw [eq24CoreInclusionOrigin_eq n] at hconn
      exact hconn
    · rintro ⟨z, hz, hconn⟩
      have hz' : z ∈ generalRectangleDualBottomCollarInnerThreeSides
          (-(n:ℤ),0) (2*n) n := by
        simp only [rectangleDualBottomCollarInnerThreeSides,
          generalRectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq] at hz ⊢
        rcases hz with hleft | hright | htop <;> omega
      refine ⟨c, Set.mem_singleton c, z, hz', ?_⟩
      change ActualConnected (rectangleDualGraph (-(n:ℤ),0) (2*n) n) D
        (parafermionicCoverEq24DualOriginVertex n) z at hconn
      rw [eq24CoreInclusionOrigin_eq n]
      exact hconn
  have hSides : generalRectangleDualBottomCollarInnerThreeSides
      (-(n:ℤ),0) (2*n) n = rectangleDualBottomCollarInnerThreeSides n := by
    ext v
    simp [generalRectangleDualBottomCollarInnerThreeSides,
      rectangleDualBottomCollarInnerThreeSides]
    omega
  rw [hleft, hright] at h
  rw [hSides] at h
  simpa [rectangleDualBottomCollarInnerGraph,
    parafermionicCoverEq24DualOriginEvent] using h

end
end PottsContinuity.FKC.FiniteFK
