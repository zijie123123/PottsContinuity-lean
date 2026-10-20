-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripFiniteSourceComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteRegionSourceComparison
public import PottsContinuity.FKC.FiniteFK.HorizontalStripWindowGeometry
public import PottsContinuity.FKC.FiniteFK.Isomorphism
public import PottsContinuity.FKC.FiniteFK.RectangleBottomCollar
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open MeasureTheory FiniteProbability

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- The local three-sided wired set, with corners included. -/
def horizontalStripWindowLocalWiredSet (m n : ℕ) (k : ℤ) (h : ℕ) :
    Set (RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n) :=
  {v | v.val ∈ rectangleLeftSide (k - (m : ℤ), (h : ℤ)) (2 * m) n ∪
    rectangleRightSide (k - (m : ℤ), (h : ℤ)) (2 * m) n ∪
    rectangleTopSide (k - (m : ℤ), (h : ℤ)) (2 * m) n}

/-- The translated bottom-center vertex in the local window rectangle. -/
def horizontalStripWindowLocalRoot (m n : ℕ) (k : ℤ) (h : ℕ) :
    RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n :=
  ⟨(k, (h : ℤ)), by
    rw [mem_latticeRectangle]
    constructor
    · constructor <;> omega
    · constructor <;> norm_cast; omega⟩

@[simp] theorem horizontalStripWindowLocalRoot_val
    (m n : ℕ) (k : ℤ) (h : ℕ) :
    (horizontalStripWindowLocalRoot m n k h).val = (k, (h : ℤ)) := rfl

/-- Actual connection from the translated bottom-center root to one of its three wired sides. -/
def horizontalStripWindowLocalConnectionEvent (m n : ℕ) (k : ℤ) (h : ℕ) :
    Set (Configuration (rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n)) :=
  {A | ∃ y : RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n,
    y ∈ horizontalStripWindowLocalWiredSet m n k h ∧
      ActualConnected (rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n) A
        (horizontalStripWindowLocalRoot m n k h) y}

theorem horizontalStripWindow_finiteSource_probability_le
    (q : ClusterWeight) (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    (measure (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)) q ξ
      (finiteRegionSourceEvent
        (horizontalStripWindowRegion N n m k h)
        (horizontalStripWindowWiredRegion N n m k h)
        (horizontalStripWindowRoot N n m k h hh hN))).toReal ≤
      (measure (rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n) q
        (BoundaryCondition.wired (horizontalStripWindowLocalWiredSet m n k h))
        (horizontalStripWindowLocalConnectionEvent m n k h)).toReal := by
  classical
  let G := rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)
  let H := horizontalStripWindowRegion N n m k h
  let W := horizontalStripWindowWiredRegion N n m k h
  let root := horizontalStripWindowRoot N n m k h hh hN
  let R := G.induce H
  let L := rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n
  let e := horizontalStripWindowGraphIso N n m k h hh hN
  let Breg : BoundaryCondition (↑H) := BoundaryCondition.wired {v | v.val ∈ W}
  let Bloc : BoundaryCondition (RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n) :=
    BoundaryCondition.wired (horizontalStripWindowLocalWiredSet m n k h)
  have hWH : W ⊆ H := horizontalStripWindowWiredRegion_subset N n m k h
  have hroot : root ∈ H := horizontalStripWindow_root_mem N n m k h hh hN
  let hrootSubtype : {v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) // v ∈ H} :=
    ⟨root, hroot⟩
  let Ereg := finiteRegionWiredConnectionEvent (G := G) H W hrootSubtype
  let Eloc := horizontalStripWindowLocalConnectionEvent m n k h
  have htop : ξ.boundary ⊆ Hᶜ ∪ W := by
    intro v hv
    exact horizontalStripTopSides_subset_windowComplement_union_wired
      N n m k h hh hN (hξ hv)
  have hsource := finiteRegionSourceEvent_probability_le_wiredRegion (G := G)
    q ξ H W hWH htop root hroot
  have hrootIso : e ((horizontalStripWindowVertexEquiv N n m k h hh hN).symm
      hrootSubtype) = hrootSubtype := e.apply_symm_apply hrootSubtype
  have hlocalRootMap : e (horizontalStripWindowLocalRoot m n k h) = hrootSubtype := by
    apply Subtype.ext
    apply Subtype.ext
    simp [e, horizontalStripWindowGraphIso, root, hrootSubtype,
      horizontalStripWindowVertexEquiv_val]
  have hlocalRoot : (horizontalStripWindowVertexEquiv N n m k h hh hN).symm
      hrootSubtype = horizontalStripWindowLocalRoot m n k h := by
    apply e.injective
    calc
      e ((horizontalStripWindowVertexEquiv N n m k h hh hN).symm hrootSubtype) =
          hrootSubtype := hrootIso
      _ = e (horizontalStripWindowLocalRoot m n k h) := hlocalRootMap.symm
  have hside (v : RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n) :
      (e v).val ∈ W ↔ v ∈ horizontalStripWindowLocalWiredSet m n k h := by
    change (horizontalStripWindowVertexEquiv N n m k h hh hN v).val ∈ W ↔ _
    simpa [horizontalStripWindowLocalWiredSet] using
      horizontalStripWindowWiredRegion_iff_sides N n m k h hh hN v
  have hpart : (boundaryConditionIso e Bloc).partition = Breg.partition := by
    apply Setoid.ext
    intro u v
    change Bloc.partition.r (e.symm u) (e.symm v) ↔ Breg.partition.r u v
    have hu : e.symm u ∈ horizontalStripWindowLocalWiredSet m n k h ↔ u.val ∈ W := by
      simpa only [e.apply_symm_apply] using (hside (e.symm u)).symm
    have hv : e.symm v ∈ horizontalStripWindowLocalWiredSet m n k h ↔ v.val ∈ W := by
      simpa only [e.apply_symm_apply] using (hside (e.symm v)).symm
    constructor
    · rintro (heq | ⟨hu', hv'⟩)
      · exact Or.inl (e.symm.injective heq)
      · exact Or.inr ⟨hu.mp hu', hv.mp hv'⟩
    · rintro (heq | ⟨hu', hv'⟩)
      · exact Or.inl (congrArg e.symm heq)
      · exact Or.inr ⟨hu.mpr hu', hv.mpr hv'⟩
  have hlaw : (law L q Bloc).map (configurationIso e) = law R q Breg := by
    calc
      (law L q Bloc).map (configurationIso e) = law R q (boundaryConditionIso e Bloc) :=
        law_configurationIso_map q e Bloc
      _ = law R q Breg := by
        rw [law_eq_of_boundary_partition_eq q _ _ hpart]
  have hmap := congrArg PMF.toMeasure hlaw
  rw [← PMF.toMeasure_map _ _ measurable_from_top] at hmap
  have hset : (configurationIso e) ⁻¹' Ereg = Eloc := by
    ext A
    change (configurationIso e A ∈ Ereg) ↔ A ∈ Eloc
    simp only [Ereg, Eloc, finiteRegionWiredConnectionEvent,
      horizontalStripWindowLocalConnectionEvent, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hyW, hyconn⟩
      refine ⟨e.symm y, (hside (e.symm y)).mp ?_, ?_⟩
      · simpa only [e.apply_symm_apply] using hyW
      · have hconn := (actualConnected_configurationIso e A
          ((horizontalStripWindowVertexEquiv N n m k h hh hN).symm hrootSubtype)
          (e.symm y)).mp (by simpa only [hrootIso, e.apply_symm_apply] using hyconn)
        exact hconn
    · rintro ⟨z, hzW, hzconn⟩
      refine ⟨e z, (hside z).mpr hzW, ?_⟩
      have hzconn' : ActualConnected L A
          ((horizontalStripWindowVertexEquiv N n m k h hh hN).symm hrootSubtype) z := by
        simpa only [hlocalRoot] using hzconn
      have hconn := (actualConnected_configurationIso e A
        ((horizontalStripWindowVertexEquiv N n m k h hh hN).symm hrootSubtype) z).mpr hzconn'
      simpa only [hrootIso] using hconn
  have hmeasure : measure R q Breg Ereg = measure L q Bloc Eloc := by
    change (law R q Breg).toMeasure Ereg = (law L q Bloc).toMeasure Eloc
    rw [← hmap]
    rw [Measure.map_apply measurable_from_top (MeasurableSet.of_discrete (s := Ereg))]
    rw [hset]
  have hmeasureReal := congrArg ENNReal.toReal hmeasure
  have hsource' : (measure G q ξ (finiteRegionSourceEvent H W root)).toReal ≤
      (measure R q Breg Ereg).toReal := by
    simpa [R, Breg, Ereg, G, H, W, hrootSubtype] using hsource
  have hbound := le_trans hsource' (le_of_eq hmeasureReal)
  simpa [Eloc, R, Breg, Bloc, root, G, H, W, hrootSubtype] using hbound

end
end PottsContinuity.FKC.FiniteFK
