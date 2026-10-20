-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxReferenceRectangle.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripOriginAspectTwoLowerBound
public import PottsContinuity.FKC.FiniteFK.RectangleTranslation
public import PottsContinuity.FKC.FiniteFK.HorizontalStripWindowTranslation
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenter
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

open MeasureTheory

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC PottsContinuity.FKC.FiniteFK
noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- Full induced square reference graph in the original slit-box coordinates.
This retains every rectangle edge, including the arc edges removed by
`slitBoxGraph`. -/
def slitBoxReferenceGraph (n : ℕ) : SimpleGraph (SlitBoxVertex n) :=
  rectangleGraph (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)

/-- The three outer sides wired for the full-square reference problem. -/
def slitBoxReferenceOuterWiredSet (n : ℕ) : Set (SlitBoxVertex n) :=
  {v | v.val ∈ rectangleLeftSide (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) ∪
    rectangleRightSide (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) ∪
    rectangleTopSide (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)}

/-- Actual connectivity from the bottom-center vertex to one of the three
wired outer sides in the full reference square. -/
def slitBoxReferenceBottomConnectionEvent (n : ℕ) :
    Set (Configuration (slitBoxReferenceGraph n)) :=
  {A | ∃ y ∈ slitBoxReferenceOuterWiredSet n,
    ActualConnected (slitBoxReferenceGraph n) A (slitBoxBottomCenterVertex n) y}

 theorem slitBoxReferenceTranslate_mem (n : ℕ)
    (v : RectangleVertex (-(n : ℤ), 0) (2*n) (2*n)) :
    latticeTranslate (0, -(n : ℤ)) v.val ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
  have hprop := v.property
  rw [mem_latticeRectangle] at hprop ⊢
  rcases hprop with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  simp only [latticeTranslate]
  constructor
  · constructor <;> omega
  · constructor <;> omega

 theorem slitBoxReferenceTranslate_back_mem (n : ℕ)
    (v : SlitBoxVertex n) :
    latticeTranslate (0, (n : ℤ)) v.val ∈ latticeRectangle (-(n : ℤ), 0) (2*n) (2*n) := by
  have hprop := v.property
  rw [mem_latticeRectangle] at hprop ⊢
  rcases hprop with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  simp only [latticeTranslate]
  constructor
  · constructor <;> omega
  · constructor <;> omega

def slitBoxReferenceTranslation (n : ℕ) :
    rectangleGraph (-(n : ℤ), 0) (2*n) (2*n) ≃g slitBoxReferenceGraph n where
  toEquiv :=
    { toFun := fun v => ⟨latticeTranslate (0, -(n : ℤ)) v.val,
        slitBoxReferenceTranslate_mem n v⟩
      invFun := fun v => ⟨latticeTranslate (0, (n : ℤ)) v.val,
        slitBoxReferenceTranslate_back_mem n v⟩
      left_inv := by
        intro v
        apply Subtype.ext
        ext <;> simp [latticeTranslate]
      right_inv := by
        intro v
        apply Subtype.ext
        ext <;> simp [latticeTranslate] }
  map_rel_iff' := by
    intro u v
    change squareLattice.Adj (latticeTranslate (0, -(n : ℤ)) u.val)
      (latticeTranslate (0, -(n : ℤ)) v.val) ↔ squareLattice.Adj u.val v.val
    exact squareLattice_adj_translate_iff (0, -(n : ℤ)) u.val v.val

@[simp] private theorem slitBoxReferenceTranslation_val (n : ℕ)
    (v : RectangleVertex (-(n : ℤ), 0) (2*n) (2*n)) :
    (slitBoxReferenceTranslation n v).val = latticeTranslate (0, -(n : ℤ)) v.val := rfl

private theorem slitBoxReference_localLeft_iff (n : ℕ)
    (v : RectangleVertex (-(n : ℤ), 0) (2*n) (2*n)) :
    v.val ∈ rectangleLeftSide (-(n : ℤ), 0) (2*n) (2*n) ↔ v.val.1 = -(n : ℤ) := by
  simp [rectangleLeftSide, v.property]

private theorem slitBoxReference_localRight_iff (n : ℕ)
    (v : RectangleVertex (-(n : ℤ), 0) (2*n) (2*n)) :
    v.val ∈ rectangleRightSide (-(n : ℤ), 0) (2*n) (2*n) ↔ v.val.1 = (n : ℤ) := by
  simp [rectangleRightSide, v.property]
  omega

private theorem slitBoxReference_localTop_iff (n : ℕ)
    (v : RectangleVertex (-(n : ℤ), 0) (2*n) (2*n)) :
    v.val ∈ rectangleTopSide (-(n : ℤ), 0) (2*n) (2*n) ↔ v.val.2 = 2*(n : ℤ) := by
  simp [rectangleTopSide, v.property]

private theorem slitBoxReference_targetLeft_iff (n : ℕ)
    (v : SlitBoxVertex n) :
    v.val ∈ rectangleLeftSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) ↔
      v.val.1 = -(n : ℤ) := by
  simp [rectangleLeftSide, v.property]

private theorem slitBoxReference_targetRight_iff (n : ℕ)
    (v : SlitBoxVertex n) :
    v.val ∈ rectangleRightSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) ↔
      v.val.1 = (n : ℤ) := by
  simp [rectangleRightSide, v.property]
  omega

private theorem slitBoxReference_targetTop_iff (n : ℕ)
    (v : SlitBoxVertex n) :
    v.val ∈ rectangleTopSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) ↔
      v.val.2 = (n : ℤ) := by
  simp [rectangleTopSide, v.property]
  omega

private theorem slitBoxReferenceTranslation_pointwise (n : ℕ)
    (v : RectangleVertex (-(n : ℤ), 0) (2*n) (2*n)) :
    v ∈ horizontalStripOriginLocalWiredSet n (2*n) ↔
      slitBoxReferenceTranslation n v ∈ slitBoxReferenceOuterWiredSet n := by
  change (v.val ∈ rectangleLeftSide (-(n : ℤ), 0) (2*n) (2*n) ∪
      rectangleRightSide (-(n : ℤ), 0) (2*n) (2*n) ∪
      rectangleTopSide (-(n : ℤ), 0) (2*n) (2*n)) ↔
    (slitBoxReferenceTranslation n v).val ∈
      rectangleLeftSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) ∪
      rectangleRightSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) ∪
      rectangleTopSide (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)
  simp only [Finset.mem_union, slitBoxReference_localLeft_iff,
    slitBoxReference_localRight_iff, slitBoxReference_localTop_iff,
    slitBoxReference_targetLeft_iff, slitBoxReference_targetRight_iff,
    slitBoxReference_targetTop_iff]
  rw [slitBoxReferenceTranslation_val]
  simp only [latticeTranslate]
  omega

private theorem slitBoxReferenceTranslation_wired (n : ℕ) :
    slitBoxReferenceTranslation n ''
      (horizontalStripOriginLocalWiredSet n (2 * n)) =
    slitBoxReferenceOuterWiredSet n := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (slitBoxReferenceTranslation_pointwise n u).1 hu
  · intro hv
    refine ⟨(slitBoxReferenceTranslation n).symm v, ?_, ?_⟩
    · have hpoint := slitBoxReferenceTranslation_pointwise n
        ((slitBoxReferenceTranslation n).symm v)
      simpa using hpoint.mpr (by simpa using hv)
    · exact (slitBoxReferenceTranslation n).apply_symm_apply v

private theorem slitBoxReferenceTranslation_root (n : ℕ) :
    slitBoxReferenceTranslation n (horizontalStripOriginLocalRoot n (2*n)) =
      slitBoxBottomCenterVertex n := by
  apply Subtype.ext
  rw [slitBoxReferenceTranslation_val]
  simp [horizontalStripOriginLocalRoot, slitBoxBottomCenterVertex_val,
    latticeTranslate]

private theorem slitBoxReferenceTranslation_event_preimage (n : ℕ) :
    (configurationIso (slitBoxReferenceTranslation n)) ⁻¹'
      slitBoxReferenceBottomConnectionEvent n =
    {A : Configuration (rectangleGraph (-(n : ℤ), 0) (2*n) (2*n)) |
      horizontalStripOriginLocalConnectionEvent n (2*n) A} := by
  ext A
  change slitBoxReferenceBottomConnectionEvent n
      ((configurationIso (slitBoxReferenceTranslation n)) A) ↔
    horizontalStripOriginLocalConnectionEvent n (2*n) A
  constructor
  · rintro ⟨y, hy, hconn⟩
    let z := (slitBoxReferenceTranslation n).symm y
    have heq : slitBoxReferenceTranslation n z = y :=
      (slitBoxReferenceTranslation n).apply_symm_apply y
    refine ⟨z, ?_, ?_⟩
    · exact (slitBoxReferenceTranslation_pointwise n z).2 (by simpa [heq] using hy)
    · have hc : ActualConnected (slitBoxReferenceGraph n)
          ((configurationIso (slitBoxReferenceTranslation n)) A)
          (slitBoxReferenceTranslation n (horizontalStripOriginLocalRoot n (2*n)))
          (slitBoxReferenceTranslation n z) := by
        simpa [heq, slitBoxReferenceTranslation_root n] using hconn
      exact (actualConnected_configurationIso (slitBoxReferenceTranslation n) A
        (horizontalStripOriginLocalRoot n (2*n)) z).mp hc
  · rintro ⟨y, hy, hconn⟩
    refine ⟨slitBoxReferenceTranslation n y,
      (slitBoxReferenceTranslation_pointwise n y).1 hy, ?_⟩
    have hc := (actualConnected_configurationIso (slitBoxReferenceTranslation n) A
      (horizontalStripOriginLocalRoot n (2*n)) y).mpr hconn
    simpa [slitBoxReferenceTranslation_root n] using hc


/-- The source-faithful full-square reference event has the same actual finite
FK mass as the translated height-`2n`, halfwidth-`n` rectangle. The graph and
boundary here are those of the full square, not the slit graph or slit arc. -/
theorem slitBoxReferenceBottomConnection_probability_lower_bound
    (q : ClusterWeight) {n : ℕ} (hn : 1 ≤ n) :
    (1 / (20 * (n : ℝ)^4) : ℝ) ≤
      (measure (slitBoxReferenceGraph n) q
        (BoundaryCondition.wired (slitBoxReferenceOuterWiredSet n))
        (slitBoxReferenceBottomConnectionEvent n)).toReal := by
  let e := slitBoxReferenceTranslation n
  let B := horizontalStripOriginLocalWiredSet n (2*n)
  let E := horizontalStripOriginLocalConnectionEvent n (2*n)
  let B' := slitBoxReferenceOuterWiredSet n
  let E' := slitBoxReferenceBottomConnectionEvent n
  have hlaw := law_configurationIso_map q e (BoundaryCondition.wired B)
  rw [boundaryConditionIso_wired_image] at hlaw
  have hmeasure :
      (measure (rectangleGraph (-(n : ℤ), 0) (2*n) (2*n)) q
        (BoundaryCondition.wired B) E).toReal =
      (measure (slitBoxReferenceGraph n) q
        (BoundaryCondition.wired B') E').toReal := by
    have hm := congrArg (fun μ : PMF (Configuration (slitBoxReferenceGraph n)) =>
      μ.toMeasure E') hlaw
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
      (MeasurableSet.of_discrete (s := E'))] at hm
    have hpre : (configurationIso e) ⁻¹' E' = E := by
      ext A
      change A ∈ (configurationIso (slitBoxReferenceTranslation n)) ⁻¹'
          slitBoxReferenceBottomConnectionEvent n ↔
        A ∈ horizontalStripOriginLocalConnectionEvent n (2*n)
      exact (Set.ext_iff.mp (slitBoxReferenceTranslation_event_preimage n)) A
    have hsets : e '' B = B' := by
      simpa [e, B, B'] using slitBoxReferenceTranslation_wired n
    rw [hpre, hsets] at hm
    simpa [FiniteFK.measure, E, E', B, B'] using congrArg ENNReal.toReal hm
  have h := horizontalStripOriginConnection_probability_lower_bound_height_two_n q hn
  simpa [slitBoxReferenceGraph] using h.trans_eq hmeasure

end
end PottsContinuity.FKC.Medial
