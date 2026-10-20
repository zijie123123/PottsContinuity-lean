module

public import PottsContinuity.Thm3.RSW.StripWindow
public import PottsContinuity.Foundations.BoxBoundary

/-!
# Actual tilted-strip carriers and finite mixed-boundary laws

DCST, TeX lines 1563–1573. A digital top vertex has a lattice neighbour
strictly above the upper supporting line. Digital bottom is defined by the
analogous lower supporting line. Top and artificial box sides take precedence
at shared boundary vertices. Thus nonintegral slopes never use equality with
a supporting line as a surrogate for the digital boundary.

The cylinder/exhaustion proofs specialize the RSW.StripWindow
construction to tilted box windows. Existence and uniqueness for i=0 are proved as
`isTiltedStripLimit_top_existsUnique` in `Thm3.Prop4.TiltedLimit`; independence of
the side boundary is not formalized. Neither is part of the definition of a
limiting measure.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Height relative to the lower supporting line, on every lattice vertex. -/
def tiltedHeight (t : ℝ) (z : ℤ × ℤ) : ℝ := (z.2 : ℝ) - t * z.1

/-- The actual infinite tilted strip of height n. -/
def tiltedStripVertices (n : ℕ) (t : ℝ) : Set (ℤ × ℤ) :=
  {z | 0 ≤ tiltedHeight t z ∧ tiltedHeight t z ≤ n}

/-- Its induced nearest-neighbour graph. -/
def tiltedStripGraph (n : ℕ) (t : ℝ) : SimpleGraph (tiltedStripVertices n t) :=
  squareLattice.induce (tiltedStripVertices n t)

/-- States on the original edges of the tilted strip. -/
abbrev TiltedConfiguration (n : ℕ) (t : ℝ) := (tiltedStripGraph n t).edgeSet → Bool

/-- Intrinsic digital top boundary, independent of finite truncations. -/
def tiltedTop (n : ℕ) (t : ℝ) (z : ℤ × ℤ) : Prop :=
  ∃ y : ℤ × ℤ, squareLattice.Adj z y ∧ (n : ℝ) < tiltedHeight t y

/-- Exactly S(n,t) intersected with the frozen square box, including all its
lattice boundary vertices. -/
noncomputable def tiltedWindow (n m : ℕ) (t : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (box m).filter (fun z => z ∈ tiltedStripVertices n t)

@[simp] theorem mem_tiltedWindow (n m : ℕ) (t : ℝ) (z : ℤ × ℤ) :
    z ∈ tiltedWindow n m t ↔ z ∈ box m ∧ z ∈ tiltedStripVertices n t := by
  classical
  simp only [tiltedWindow, Finset.mem_filter]

/-- i=0 wires the intrinsic top only; i=1 also wires artificial box sides
into the same block. All other vertices remain singleton classes. -/
def tiltedWindowWiredVertices (n m : ℕ) (t : ℝ) (i : Fin 2) :
    Set (tiltedWindow n m t : Set (ℤ × ℤ)) :=
  {z | tiltedTop n t z.1 ∨ i = 1 ∧ z.1 ∈ vertexBoundary (box m)}

/-- The actual finite boundary partition, with a single wired block. -/
def tiltedWindowBoundary (n m : ℕ) (t : ℝ) (i : Fin 2) :
    PD.FK.BoundaryCondition (tiltedWindow n m t : Set (ℤ × ℤ)) :=
  PD.FK.BoundaryCondition.wired (tiltedWindowWiredVertices n m t i)

/-- A finite pattern read on actual finite-window edges. -/
def tiltedWindowCylinder (n m : ℕ) (t : ℝ)
    (A : Finset (tiltedStripGraph n t).edgeSet) (ξ : TiltedConfiguration n t)
    (ω : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  ∀ e ∈ A, ∃ f : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet,
    Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1 ∧ ω f = ξ e

/-- Its mixed-boundary FK probability, at independent interior parameters. -/
noncomputable def tiltedWindowCylinderProbability (θ : PD.FK.Parameters)
    (n : ℕ) (t : ℝ) (i : Fin 2) (m : ℕ)
    (A : Finset (tiltedStripGraph n t).edgeSet) (ξ : TiltedConfiguration n t) : ℝ :=
  RSW.finiteBoundaryEventProbability (tiltedWindow n m t) θ
    (tiltedWindowBoundary n m t i) (tiltedWindowCylinder n m t A ξ)

/-- The genuine cylinder-limit predicate, on the actual strip configuration
carrier. This predicate asserts convergence, not the existence of a limit. -/
def IsTiltedStripLimit (θ : PD.FK.Parameters) (n : ℕ) (t : ℝ) (i : Fin 2)
    (ν : Measure (TiltedConfiguration n t)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ (A : Finset (tiltedStripGraph n t).edgeSet)
    (ξ : TiltedConfiguration n t),
    Tendsto (fun m => tiltedWindowCylinderProbability θ n t i m A ξ) atTop
      (𝓝 (ν.real {ω | ∀ e ∈ A, ω e = ξ e}))

/-- The root is present at every nonnegative height and truncation radius. -/
def tiltedWindowOrigin (n m : ℕ) (t : ℝ) : (tiltedWindow n m t : Set (ℤ × ℤ)) :=
  ⟨(0, 0), by simp [tiltedStripVertices, tiltedHeight, box]⟩

/-- Actual open connection from 0 to the wired arc; the wiring itself adds
no open edges to this event. -/
def tiltedTouchEvent (n m : ℕ) (t : ℝ)
    (ω : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  ∃ z ∈ tiltedWindowWiredVertices n m t 1,
    (rcOpenGraph (tiltedWindow n m t) ω).Reachable (tiltedWindowOrigin n m t) z

/-- The finite probability in Lemma 6, at any independent interior parameters. -/
noncomputable def tiltedTouchProbability (θ : PD.FK.Parameters) (n m : ℕ) (t : ℝ) : ℝ :=
  RSW.finiteBoundaryEventProbability (tiltedWindow n m t) θ
    (tiltedWindowBoundary n m t 1) (tiltedTouchEvent n m t)

/-- Increasing the box radius retains every original vertex. -/
theorem tiltedWindow_mono (n : ℕ) (t : ℝ) : Monotone (fun m => tiltedWindow n m t) := by
  intro M N hMN z hz
  obtain ⟨hzM, hzS⟩ := (mem_tiltedWindow n M t z).mp hz
  refine (mem_tiltedWindow n N t z).mpr ⟨?_, hzS⟩
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hzM ⊢
  omega

/-- A strip vertex is present once both coordinates lie in the box. -/
theorem mem_tiltedWindow_of_abs_le (n m : ℕ) (t : ℝ) (z : tiltedStripVertices n t)
    (hx : |z.1.1| ≤ (m : ℤ)) (hy : |z.1.2| ≤ (m : ℤ)) :
    z.1 ∈ tiltedWindow n m t := by
  exact (mem_tiltedWindow n m t z.1).mpr
    ⟨(Foundations.mem_box_iff_abs_le m z.1).mpr ⟨hx, hy⟩, z.2⟩

/-- Every original strip edge is eventually present, without a change of state carrier. -/
theorem eventually_tiltedWindow_edge_lift (n : ℕ) (t : ℝ)
    (e : (tiltedStripGraph n t).edgeSet) :
    ∀ᶠ m : ℕ in atTop,
      ∃ f : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    filter_upwards [eventually_ge_atTop
      (u.1.1.natAbs + u.1.2.natAbs + v.1.1.natAbs + v.1.2.natAbs)] with m hm
    have hu : u.1 ∈ tiltedWindow n m t := by
      apply mem_tiltedWindow_of_abs_le
      all_goals rw [← Int.natCast_natAbs]; exact_mod_cast (by omega : _ ≤ m)
    have hv : v.1 ∈ tiltedWindow n m t := by
      apply mem_tiltedWindow_of_abs_le
      all_goals rw [← Int.natCast_natAbs]; exact_mod_cast (by omega : _ ≤ m)
    let u' : (tiltedWindow n m t : Set (ℤ × ℤ)) := ⟨u.1, hu⟩
    let v' : (tiltedWindow n m t : Set (ℤ × ℤ)) := ⟨v.1, hv⟩
    have hadj : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).Adj u' v' :=
      (tiltedStripGraph n t).mem_edgeSet.mp he
    exact ⟨⟨s(u', v'), (squareLattice.induce _).mem_edgeSet.mpr hadj⟩, rfl⟩

/-- A finite strip pattern is eventually fully supported by the windows. -/
theorem eventually_tiltedWindow_finset_edge_lift (n : ℕ) (t : ℝ)
    (A : Finset (tiltedStripGraph n t).edgeSet) :
    ∀ᶠ m : ℕ in atTop, ∀ e ∈ A,
      ∃ f : (squareLattice.induce (tiltedWindow n m t : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1 := by
  exact (eventually_all_finset A).mpr fun e _ => eventually_tiltedWindow_edge_lift n t e

/-- Uniqueness for a fixed lateral convention; independence of the convention is not claimed. -/
theorem isTiltedStripLimit_unique (θ : PD.FK.Parameters) (n : ℕ) (t : ℝ) (i : Fin 2)
    (μ ν : Measure (TiltedConfiguration n t))
    (hμ : IsTiltedStripLimit θ n t i μ) (hν : IsTiltedStripLimit θ n t i ν) : μ = ν := by
  let : IsProbabilityMeasure μ := hμ.1
  let : IsProbabilityMeasure ν := hν.1
  refine PD.ext_of_cylinders μ ν (fun _ => false) ?_
  intro A ξ
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (tendsto_nhds_unique (hμ.2 A ξ) (hν.2 A ξ))

end PottsContinuity.Thm3.Prop4
