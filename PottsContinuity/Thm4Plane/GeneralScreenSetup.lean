module

public import PottsContinuity.Thm4Plane.GeneralEScreen
public import PottsContinuity.Thm4Plane.ScreenConnector
public import PottsContinuity.FKC.FiniteFK.SlitScreenCrossingEvents

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC.Medial

/-! # Rounded all-scale screen geometry

The dual face center associated with a face base `(x,y)` is
`(x+1/2,y+1/2)`.  Convert each source half-integer rectangle to integer face
bases by taking the ceiling of each lower coordinate and the floor of each
upper coordinate.  This matters away from multiples of 16; at `n = 16*m` the
carriers agree with the finite-probability screen geometry.
-/

def generalScreenScale (n : ℕ) : ℕ := (n + 15) / 16

def generalScreenFiveScale (n : ℕ) : ℕ := (5 * n) / 16

def generalScreenThreeQuarterScale (n : ℕ) : ℕ := (3 * n) / 4

def generalScreenEighthScale (n : ℕ) : ℕ := (n + 7) / 8

/-- The rounded right tall rectangle of dual face bases. -/
def generalScreenRightFaceBases (n : ℕ) : Finset LatticeVertex :=
  Finset.Icc (generalScreenScale n : ℤ)
      ((generalScreenFiveScale n : ℤ) - 1) ×ˢ
    Finset.Icc (-(n : ℤ) - 1) (n : ℤ)

/-- The rounded left tall rectangle of dual face bases. -/
def generalScreenLeftFaceBases (n : ℕ) : Finset LatticeVertex :=
  Finset.Icc (-(generalScreenFiveScale n : ℤ))
      (-(generalScreenScale n : ℤ) - 1) ×ˢ
    Finset.Icc (-(n : ℤ) - 1) (n : ℤ)

/-- The rounded middle connector rectangle of dual face bases. -/
def generalScreenMiddleFaceBases (n : ℕ) : Finset LatticeVertex :=
  Finset.Icc (-(generalScreenFiveScale n : ℤ))
      ((generalScreenFiveScale n : ℤ) - 1) ×ˢ
    Finset.Icc (-(generalScreenThreeQuarterScale n : ℤ))
      (-(generalScreenEighthScale n : ℤ) - 1)

/-- The right face bases are exactly the integer centers in the source's
half-integer rectangle, expressed after clearing denominators. -/
theorem generalScreenRightFaceBases_mem_iff (n : ℕ) (x y : ℤ) :
    (x, y) ∈ generalScreenRightFaceBases n ↔
      (n : ℤ) ≤ 16*x ∧ 16*(x+1) ≤ 5*(n : ℤ) ∧
        -(n : ℤ)-1 ≤ y ∧ y ≤ n := by
  simp [generalScreenRightFaceBases, generalScreenScale, generalScreenFiveScale,
    Finset.mem_product, Finset.mem_Icc]
  omega

/-- The left face bases are exactly the integer centers in the source's
half-integer rectangle, expressed after clearing denominators. -/
theorem generalScreenLeftFaceBases_mem_iff (n : ℕ) (x y : ℤ) :
    (x, y) ∈ generalScreenLeftFaceBases n ↔
      -5*(n : ℤ) ≤ 16*x ∧ 16*(x+1) ≤ -(n : ℤ) ∧
        -(n : ℤ)-1 ≤ y ∧ y ≤ n := by
  simp [generalScreenLeftFaceBases, generalScreenScale, generalScreenFiveScale,
    Finset.mem_product, Finset.mem_Icc]
  omega

/-- The connector face bases are exactly the integer centers in the source's
half-integer rectangle, expressed after clearing denominators. -/
theorem generalScreenMiddleFaceBases_mem_iff (n : ℕ) (x y : ℤ) :
    (x, y) ∈ generalScreenMiddleFaceBases n ↔
      -5*(n : ℤ) ≤ 16*x ∧ 16*(x+1) ≤ 5*(n : ℤ) ∧
        -3*(n : ℤ) ≤ 4*y ∧ 8*(y+1) ≤ -(n : ℤ) := by
  simp [generalScreenMiddleFaceBases, generalScreenFiveScale,
    generalScreenThreeQuarterScale, generalScreenEighthScale,
    Finset.mem_product, Finset.mem_Icc]
  omega

/-- Bottom and top terminals use the boundary dual rows of the slit box. -/
def generalScreenBottomTerminals (n : ℕ) (F : Finset LatticeVertex) :
    Set LatticeVertex := {v | v ∈ F ∧ v.2 = -(n : ℤ) - 1}

def generalScreenTopTerminals (n : ℕ) (F : Finset LatticeVertex) :
    Set LatticeVertex := {v | v ∈ F ∧ v.2 = (n : ℤ)}

/-- The finite closed-dual graph on actual slit-box edges, with both face
endpoints restricted to the selected finite carrier. -/
def generalScreenActualClosedDualGraph (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (F : Finset LatticeVertex) :
    SimpleGraph LatticeVertex where
  Adj u v := ∃ d : LatticeBond, ∃ e : (slitBoxGraph n).edgeSet,
    latticeBondEdge (primalBondOfDual d) = slitBoxEdgeEmbedding n e ∧
      e ∉ A ∧
      (u = d.source ∧ v = d.target ∨ u = d.target ∧ v = d.source) ∧
      u ∈ F ∧ v ∈ F
  symm := by
    constructor
    intro u v h
    rcases h with ⟨d, e, he, hnot, huv, huF, hvF⟩
    rcases huv with huv | huv
    · exact ⟨d, e, he, hnot, Or.inr ⟨huv.2, huv.1⟩, hvF, huF⟩
    · exact ⟨d, e, he, hnot, Or.inl ⟨huv.2, huv.1⟩, hvF, huF⟩
  loopless := by
    constructor
    intro u h
    rcases h with ⟨d, e, _, _, huv, _, _⟩
    rcases huv with huv | huv
    · exact d.source_ne_target (huv.1.symm.trans huv.2)
    · exact d.source_ne_target (huv.2.symm.trans huv.1)

/-- The rounded connector event `C`: actual closed-dual side crossings are
joined by a path in the middle rectangle. -/
def generalCEvent (n : ℕ) :
    Set (Configuration (slitBoxGraph n)) :=
  {A |
    ∃ lb ∈ generalScreenBottomTerminals n (generalScreenLeftFaceBases n),
    ∃ lt ∈ generalScreenTopTerminals n (generalScreenLeftFaceBases n),
    ∃ pL : (generalScreenActualClosedDualGraph n A
      (generalScreenLeftFaceBases n)).Walk lb lt,
    ∃ rb ∈ generalScreenBottomTerminals n (generalScreenRightFaceBases n),
    ∃ rt ∈ generalScreenTopTerminals n (generalScreenRightFaceBases n),
    ∃ pR : (generalScreenActualClosedDualGraph n A
      (generalScreenRightFaceBases n)).Walk rb rt,
    ∃ u v, u ∈ pL.support ∧ v ∈ pR.support ∧
      (generalScreenActualClosedDualGraph n A
        (generalScreenMiddleFaceBases n)).Reachable u v}

private theorem generalScreenScale_sixteen (m : ℕ) :
    generalScreenScale (16 * m) = m := by
  dsimp [generalScreenScale]
  omega

private theorem generalScreenFiveScale_sixteen (m : ℕ) :
    generalScreenFiveScale (16 * m) = 5 * m := by
  dsimp [generalScreenFiveScale]
  omega

private theorem generalScreenThreeQuarterScale_sixteen (m : ℕ) :
    generalScreenThreeQuarterScale (16 * m) = 12 * m := by
  dsimp [generalScreenThreeQuarterScale]
  omega

private theorem generalScreenEighthScale_sixteen (m : ℕ) :
    generalScreenEighthScale (16 * m) = 2 * m := by
  dsimp [generalScreenEighthScale]
  omega

theorem generalScreenRightFaceBases_sixteen (m : ℕ) :
    generalScreenRightFaceBases (16 * m) = slitScreenRightFaceBases m := by
  ext ⟨x, y⟩
  simp [generalScreenRightFaceBases, slitScreenRightFaceBases,
    Finset.mem_product, Finset.mem_Icc, generalScreenScale_sixteen,
    generalScreenFiveScale_sixteen]

theorem generalScreenLeftFaceBases_sixteen (m : ℕ) :
    generalScreenLeftFaceBases (16 * m) = slitScreenLeftFaceBases m := by
  ext ⟨x, y⟩
  simp [generalScreenLeftFaceBases, slitScreenLeftFaceBases,
    Finset.mem_product, Finset.mem_Icc, generalScreenScale_sixteen,
    generalScreenFiveScale_sixteen]

theorem generalScreenMiddleFaceBases_sixteen (m : ℕ) :
    generalScreenMiddleFaceBases (16 * m) = slitScreenMiddleFaceBases m := by
  ext ⟨x, y⟩
  simp [generalScreenMiddleFaceBases, slitScreenMiddleFaceBases,
    Finset.mem_product, Finset.mem_Icc, generalScreenFiveScale_sixteen,
    generalScreenThreeQuarterScale_sixteen,
    generalScreenEighthScale_sixteen]

private theorem generalScreenBottomTerminals_sixteen (m : ℕ)
    (F : Finset LatticeVertex) :
    generalScreenBottomTerminals (16 * m) F =
      slitScreenBottomTerminals m F := by
  ext v
  simp [generalScreenBottomTerminals, slitScreenBottomTerminals]

private theorem generalScreenTopTerminals_sixteen (m : ℕ)
    (F : Finset LatticeVertex) :
    generalScreenTopTerminals (16 * m) F =
      slitScreenTopTerminals m F := by
  ext v
  simp [generalScreenTopTerminals, slitScreenTopTerminals]

private theorem generalScreenActualClosedDualGraph_sixteen (m : ℕ)
    (A : Configuration (slitBoxGraph (16 * m))) (F : Finset LatticeVertex) :
    generalScreenActualClosedDualGraph (16 * m) A F =
      slitScreenActualConfigurationClosedDualGraph m A F := rfl

private theorem generalScreenLeftGraph_sixteen (m : ℕ)
    (A : Configuration (slitBoxGraph (16 * m))) :
    generalScreenActualClosedDualGraph (16 * m) A
        (generalScreenLeftFaceBases (16 * m)) =
      slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenLeftFaceBases m) := by
  rw [generalScreenLeftFaceBases_sixteen]
  exact generalScreenActualClosedDualGraph_sixteen m A _

private theorem generalScreenRightGraph_sixteen (m : ℕ)
    (A : Configuration (slitBoxGraph (16 * m))) :
    generalScreenActualClosedDualGraph (16 * m) A
        (generalScreenRightFaceBases (16 * m)) =
      slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenRightFaceBases m) := by
  rw [generalScreenRightFaceBases_sixteen]
  exact generalScreenActualClosedDualGraph_sixteen m A _

private theorem generalScreenMiddleGraph_sixteen (m : ℕ)
    (A : Configuration (slitBoxGraph (16 * m))) :
    generalScreenActualClosedDualGraph (16 * m) A
        (generalScreenMiddleFaceBases (16 * m)) =
      slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenMiddleFaceBases m) := by
  rw [generalScreenMiddleFaceBases_sixteen]
  exact generalScreenActualClosedDualGraph_sixteen m A _

theorem generalCEvent_sixteen_eq (m : ℕ) :
    generalCEvent (16 * m) = slitScreenConnectorEvent m := by
  ext A
  constructor
  · rintro ⟨lb, hlb, lt, hlt, pL, rb, hrb, rt, hrt, pR, u, v,
      hu, hv, hmid⟩
    have hL := generalScreenLeftGraph_sixteen m A
    have hR := generalScreenRightGraph_sixteen m A
    have hM := generalScreenMiddleGraph_sixteen m A
    have hLle : generalScreenActualClosedDualGraph (16 * m) A
        (generalScreenLeftFaceBases (16 * m)) ≤
        slitScreenActualConfigurationClosedDualGraph m A
          (slitScreenLeftFaceBases m) := by
      rw [hL]
    have hRle : generalScreenActualClosedDualGraph (16 * m) A
        (generalScreenRightFaceBases (16 * m)) ≤
        slitScreenActualConfigurationClosedDualGraph m A
          (slitScreenRightFaceBases m) := by
      rw [hR]
    have hMle : generalScreenActualClosedDualGraph (16 * m) A
        (generalScreenMiddleFaceBases (16 * m)) ≤
        slitScreenActualConfigurationClosedDualGraph m A
          (slitScreenMiddleFaceBases m) := by
      rw [hM]
    have hlb' : lb ∈ slitScreenBottomTerminals m
        (slitScreenLeftFaceBases m) := by
      simpa only [generalScreenBottomTerminals_sixteen,
        generalScreenLeftFaceBases_sixteen] using hlb
    have hlt' : lt ∈ slitScreenTopTerminals m
        (slitScreenLeftFaceBases m) := by
      simpa only [generalScreenTopTerminals_sixteen,
        generalScreenLeftFaceBases_sixteen] using hlt
    have hrb' : rb ∈ slitScreenBottomTerminals m
        (slitScreenRightFaceBases m) := by
      simpa only [generalScreenBottomTerminals_sixteen,
        generalScreenRightFaceBases_sixteen] using hrb
    have hrt' : rt ∈ slitScreenTopTerminals m
        (slitScreenRightFaceBases m) := by
      simpa only [generalScreenTopTerminals_sixteen,
        generalScreenRightFaceBases_sixteen] using hrt
    refine ⟨lb, hlb', lt, hlt', pL.mapLe hLle, rb, hrb', rt, hrt',
      pR.mapLe hRle, u, v, ?_, ?_, ?_⟩
    · simpa using hu
    · simpa using hv
    · exact hmid.mono hMle
  · rintro ⟨lb, hlb, lt, hlt, pL, rb, hrb, rt, hrt, pR, u, v,
      hu, hv, hmid⟩
    have hL := generalScreenLeftGraph_sixteen m A
    have hR := generalScreenRightGraph_sixteen m A
    have hM := generalScreenMiddleGraph_sixteen m A
    have hLle : slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenLeftFaceBases m) ≤
        generalScreenActualClosedDualGraph (16 * m) A
          (generalScreenLeftFaceBases (16 * m)) := by
      rw [← hL]
    have hRle : slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenRightFaceBases m) ≤
        generalScreenActualClosedDualGraph (16 * m) A
          (generalScreenRightFaceBases (16 * m)) := by
      rw [← hR]
    have hMle : slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenMiddleFaceBases m) ≤
        generalScreenActualClosedDualGraph (16 * m) A
          (generalScreenMiddleFaceBases (16 * m)) := by
      rw [← hM]
    have hlb' : lb ∈ generalScreenBottomTerminals (16 * m)
        (generalScreenLeftFaceBases (16 * m)) := by
      simpa only [generalScreenBottomTerminals_sixteen,
        generalScreenLeftFaceBases_sixteen] using hlb
    have hlt' : lt ∈ generalScreenTopTerminals (16 * m)
        (generalScreenLeftFaceBases (16 * m)) := by
      simpa only [generalScreenTopTerminals_sixteen,
        generalScreenLeftFaceBases_sixteen] using hlt
    have hrb' : rb ∈ generalScreenBottomTerminals (16 * m)
        (generalScreenRightFaceBases (16 * m)) := by
      simpa only [generalScreenBottomTerminals_sixteen,
        generalScreenRightFaceBases_sixteen] using hrb
    have hrt' : rt ∈ generalScreenTopTerminals (16 * m)
        (generalScreenRightFaceBases (16 * m)) := by
      simpa only [generalScreenTopTerminals_sixteen,
        generalScreenRightFaceBases_sixteen] using hrt
    refine ⟨lb, hlb', lt, hlt', pL.mapLe hLle, rb, hrb', rt, hrt',
      pR.mapLe hRle, u, v, ?_, ?_, ?_⟩
    · simpa using hu
    · simpa using hv
    · exact hmid.mono hMle

end PottsContinuity.Thm4Plane
