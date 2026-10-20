-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripWindowTranslation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteSourceComparison
public import PottsContinuity.FKC.FiniteFK.RectangleTranslation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
noncomputable section

attribute [local instance] configurationMeasurableSpace

 theorem windowTranslation_mem (m n : ℕ) (k : ℤ) (h : ℕ)
    (v : LatticeVertex) (hv : v ∈ latticeRectangle (k - (m : ℤ), (h : ℤ)) (2 * m) n) :
    latticeTranslate (-k, -(h : ℤ)) v ∈ latticeRectangle (-(m : ℤ), 0) (2 * m) n := by
  simp only [mem_latticeRectangle] at hv ⊢
  rcases v with ⟨vx, vy⟩
  rcases hv with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  simp only [latticeTranslate]
  constructor
  · constructor <;> omega
  · constructor <;> omega

 theorem windowTranslation_back_mem (m n : ℕ) (k : ℤ) (h : ℕ)
    (v : LatticeVertex) (hv : v ∈ latticeRectangle (-(m : ℤ), 0) (2 * m) n) :
    latticeTranslate (k, (h : ℤ)) v ∈ latticeRectangle (k - (m : ℤ), (h : ℤ)) (2 * m) n := by
  simp only [mem_latticeRectangle] at hv ⊢
  rcases v with ⟨vx, vy⟩
  rcases hv with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  simp only [latticeTranslate]
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- Translation from the local source window to the window based at the origin. -/
def horizontalStripWindowTranslationIso (m n : ℕ) (k : ℤ) (h : ℕ) :
    rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n ≃g
      rectangleGraph (-(m : ℤ), 0) (2 * m) n where
  toEquiv :=
    { toFun := fun v => ⟨latticeTranslate (-k, -(h : ℤ)) v.val,
        windowTranslation_mem m n k h v.val v.property⟩
      invFun := fun v => ⟨latticeTranslate (k, (h : ℤ)) v.val,
        windowTranslation_back_mem m n k h v.val v.property⟩
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
    change squareLattice.Adj (latticeTranslate (-k, -(h : ℤ)) u.val)
      (latticeTranslate (-k, -(h : ℤ)) v.val) ↔ squareLattice.Adj u.val v.val
    exact squareLattice_adj_translate_iff (-k, -(h : ℤ)) u.val v.val

@[simp] theorem horizontalStripWindowTranslationIso_val
    (m n : ℕ) (k : ℤ) (h : ℕ)
    (v : RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n) :
    (horizontalStripWindowTranslationIso m n k h v).val =
      latticeTranslate (-k, -(h : ℤ)) v.val := rfl

def stripConnectionEvent {V : Type*} [Finite V] (G : SimpleGraph V)
    (S : Set V) (x : V) : Set (Configuration G) :=
  {A | ∃ y, y ∈ S ∧ ActualConnected G A x y}

private theorem stripConnectionEvent_preimage_iso
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (S : Set V) (T : Set W) (x : V)
    (hS : ∀ y, y ∈ S ↔ e y ∈ T) :
    (configurationIso e) ⁻¹' stripConnectionEvent H T (e x) =
      stripConnectionEvent G S x := by
  ext A
  constructor
  · rintro ⟨y, hyT, hconn⟩
    have hyS : e.symm y ∈ S := (hS (e.symm y)).2 (by simpa using hyT)
    refine ⟨e.symm y, hyS, ?_⟩
    exact (actualConnected_configurationIso e A x (e.symm y)).mp (by
      simpa using hconn)
  · rintro ⟨y, hyS, hconn⟩
    refine ⟨e y, (hS y).1 hyS, ?_⟩
    exact (actualConnected_configurationIso e A x y).mpr hconn

private theorem rectangleLaw_iso_map_event
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (q : ClusterWeight) (e : G ≃g H) (S : Set V) (T : Set W)
    (x : V) (hS : ∀ y, y ∈ S ↔ e y ∈ T) :
    measure G q (BoundaryCondition.wired S)
        (stripConnectionEvent G S x) =
      measure H q (BoundaryCondition.wired T)
        (stripConnectionEvent H T (e x)) := by
  let f := configurationIso e
  have himage : e '' S = T := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hS y).1 hy
    · intro hz
      refine ⟨e.symm z, (hS (e.symm z)).2 ?_, e.apply_symm_apply z⟩
      simpa using hz
  have hmap : (law G q (BoundaryCondition.wired S)).map f =
      law H q (BoundaryCondition.wired T) := by
    rw [law_configurationIso_map]
    rw [boundaryConditionIso_wired_image]
    simp [himage]
  have hpre : f ⁻¹' stripConnectionEvent H T (e x) =
      stripConnectionEvent G S x :=
    stripConnectionEvent_preimage_iso e S T x hS
  change ((law G q (BoundaryCondition.wired S)).toMeasure
      (stripConnectionEvent G S x)) =
    ((law H q (BoundaryCondition.wired T)).toMeasure
      (stripConnectionEvent H T (e x)))
  symm
  rw [← hmap]
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (MeasurableSet.of_discrete (s := stripConnectionEvent H T (e x)))]
  rw [hpre]

/-- The three wired sides in the origin-based local window, on the literal
rectangle carrier with lower-left corner `(-m,0)`. -/
def horizontalStripOriginLocalWiredSet (m n : ℕ) :
    Set (RectangleVertex (-(m : ℤ), 0) (2 * m) n) :=
  {v | v.val ∈ rectangleLeftSide (-(m : ℤ), 0) (2 * m) n ∪
    rectangleRightSide (-(m : ℤ), 0) (2 * m) n ∪
    rectangleTopSide (-(m : ℤ), 0) (2 * m) n}

def horizontalStripOriginLocalRoot (m n : ℕ) :
    RectangleVertex (-(m : ℤ), 0) (2 * m) n :=
  ⟨(0, 0), by
    rw [mem_latticeRectangle]
    constructor
    · constructor <;> omega
    · constructor <;> norm_num⟩
def horizontalStripOriginLocalConnectionEvent (m n : ℕ) :
    Set (Configuration (rectangleGraph (-(m : ℤ), 0) (2 * m) n)) :=
  {A | ∃ y, y ∈ horizontalStripOriginLocalWiredSet m n ∧
    ActualConnected (rectangleGraph (-(m : ℤ), 0) (2 * m) n) A
      (horizontalStripOriginLocalRoot m n) y}

private theorem horizontalStripWindowLocalWiredSet_translation
    (m n : ℕ) (k : ℤ) (h : ℕ)
    (v : RectangleVertex (k - (m : ℤ), (h : ℤ)) (2 * m) n) :
    v ∈ horizontalStripWindowLocalWiredSet m n k h ↔
      horizontalStripWindowTranslationIso m n k h v ∈
        horizontalStripOriginLocalWiredSet m n := by
  change v.val ∈
      rectangleLeftSide (k - (m : ℤ), (h : ℤ)) (2 * m) n ∪
        rectangleRightSide (k - (m : ℤ), (h : ℤ)) (2 * m) n ∪
        rectangleTopSide (k - (m : ℤ), (h : ℤ)) (2 * m) n ↔
    (horizontalStripWindowTranslationIso m n k h v).val ∈
      rectangleLeftSide (-(m : ℤ), 0) (2 * m) n ∪
        rectangleRightSide (-(m : ℤ), 0) (2 * m) n ∪
        rectangleTopSide (-(m : ℤ), 0) (2 * m) n
  rw [horizontalStripWindowTranslationIso_val]
  simp only [rectangleLeftSide, rectangleRightSide, rectangleTopSide,
    Finset.mem_union, Finset.mem_filter,
    latticeRectangle, Finset.mem_product, Finset.mem_Icc, latticeTranslate]
  rcases v.val with ⟨vx, vy⟩
  omega



/-- The local wired connection probability is invariant under translation of
the window, with the event and all three wired sides transported literally. -/
theorem horizontalStripWindowLocalConnection_probability_eq_origin
    (q : ClusterWeight) (m n : ℕ) (k : ℤ) (h : ℕ) :
    measure (rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n) q
      (BoundaryCondition.wired (horizontalStripWindowLocalWiredSet m n k h))
      (horizontalStripWindowLocalConnectionEvent m n k h) =
    measure (rectangleGraph (-(m : ℤ), 0) (2 * m) n) q
      (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
      (horizontalStripOriginLocalConnectionEvent m n) := by
  let e := horizontalStripWindowTranslationIso m n k h
  have hS : ∀ y, y ∈ horizontalStripWindowLocalWiredSet m n k h ↔
      e y ∈ horizontalStripOriginLocalWiredSet m n := by
    intro y
    exact horizontalStripWindowLocalWiredSet_translation m n k h y
  have hx : e (horizontalStripWindowLocalRoot m n k h) =
      horizontalStripOriginLocalRoot m n := by
    apply Subtype.ext
    simp [e, horizontalStripWindowTranslationIso,
      horizontalStripWindowLocalRoot, horizontalStripOriginLocalRoot, latticeTranslate]
  have hevent : stripConnectionEvent
      (rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n)
      (horizontalStripWindowLocalWiredSet m n k h)
      (horizontalStripWindowLocalRoot m n k h) =
      horizontalStripWindowLocalConnectionEvent m n k h := by
    rfl
  have htarget : stripConnectionEvent
      (rectangleGraph (-(m : ℤ), 0) (2 * m) n)
      (horizontalStripOriginLocalWiredSet m n)
      (e (horizontalStripWindowLocalRoot m n k h)) =
      horizontalStripOriginLocalConnectionEvent m n := by
    rw [hx]
    rfl
  rw [← hevent, ← htarget]
  exact rectangleLaw_iso_map_event q e
    (horizontalStripWindowLocalWiredSet m n k h)
    (horizontalStripOriginLocalWiredSet m n)
    (horizontalStripWindowLocalRoot m n k h) hS

/-- Finite source comparison with its local FK event normalized to the
origin-based window. -/
theorem horizontalStripWindow_finiteSource_probability_le_origin
    (q : ClusterWeight) (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    (measure (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)) q ξ
      (finiteRegionSourceEvent
        (horizontalStripWindowRegion N n m k h)
        (horizontalStripWindowWiredRegion N n m k h)
        (horizontalStripWindowRoot N n m k h hh hN))).toReal ≤
    (measure (rectangleGraph (-(m : ℤ), 0) (2 * m) n) q
      (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
      (horizontalStripOriginLocalConnectionEvent m n)).toReal := by
  calc
    _ ≤ (measure (rectangleGraph (k - (m : ℤ), (h : ℤ)) (2 * m) n) q
        (BoundaryCondition.wired (horizontalStripWindowLocalWiredSet m n k h))
        (horizontalStripWindowLocalConnectionEvent m n k h)).toReal :=
      horizontalStripWindow_finiteSource_probability_le q N n m k h hh ξ hξ hN
    _ = _ := congrArg ENNReal.toReal
      (horizontalStripWindowLocalConnection_probability_eq_origin q m n k h)

end
end PottsContinuity.FKC.FiniteFK
