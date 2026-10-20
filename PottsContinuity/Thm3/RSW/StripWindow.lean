module

public import PottsContinuity.Thm3.RSW.FiniteBoundary
public import PottsContinuity.PD.Infra.CylinderUniqueness

/-!
# Top-wired strip windows and their genuine cylinder-limit predicate

The strip in Lemma 2 is ℤ × [-n,3n]. Lateral window boundary conditions are
kept explicit: `i=0` wires just the top row, whereas `i=1` wires top and sides
together. No existence or independence of these lateral choices is assumed.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.RSW

/-- Vertex set of the unbounded strip in Lemma 2. -/
def stripVertices (n : ℕ) : Set (ℤ × ℤ) :=
  {z | -(n : ℤ) ≤ z.2 ∧ z.2 ≤ 3 * (n : ℤ)}

/-- The nearest-neighbour graph induced on the whole strip. -/
def stripGraph (n : ℕ) : SimpleGraph (stripVertices n) :=
  squareLattice.induce (stripVertices n)

/-- The actual strip configuration carrier. -/
abbrev StripConfiguration (n : ℕ) := (stripGraph n).edgeSet → Bool

/-- A finite horizontal window of the strip. -/
def stripWindow (n m : ℕ) : Finset (ℤ × ℤ) :=
  latticeRectangle (-(m : ℤ)) m (-(n : ℤ)) (3 * (n : ℤ))

/-- One wired top arc; `i=1` additionally wires both lateral arcs into that
same class. Corner vertices follow the wired-side convention. -/
def stripWindowWiredVertices (n m : ℕ) (i : Fin 2) :
    Set (stripWindow n m : Set (ℤ × ℤ)) :=
  {v | v.1.2 = 3 * (n : ℤ) ∨
    i = 1 ∧ (v.1.1 = -(m : ℤ) ∨ v.1.1 = m)}

/-- The finite mixed boundary partition used in a strip approximation. -/
def stripWindowBoundary (n m : ℕ) (i : Fin 2) :
    PD.FK.BoundaryCondition (stripWindow n m : Set (ℤ × ℤ)) :=
  PD.FK.BoundaryCondition.wired (stripWindowWiredVertices n m i)

/-- A pattern on finitely many strip edges, read on a finite window. Edges
not yet present do not satisfy the cylinder; no arbitrary extension is used. -/
def stripWindowCylinder (n m : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n)
    (ω : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet → Bool) : Prop :=
  ∀ e ∈ A, ∃ f : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet,
    Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1 ∧ ω f = ξ e

/-- The finite top-wired strip-window probability of an actual cylinder. -/
noncomputable def stripWindowCylinderProbability (θ : PD.FK.Parameters)
    (n : ℕ) (i : Fin 2) (m : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n) : ℝ :=
  finiteBoundaryEventProbability (stripWindow n m) θ (stripWindowBoundary n m i)
    (stripWindowCylinder n m A ξ)

/-- An actual probability measure on strip configurations is a limit of the
specified top-wired window sequence, tested on every finite cylinder pattern.
This definition asserts convergence, not existence or lateral-boundary independence. -/
def IsTopWiredStripLimit (θ : PD.FK.Parameters) (n : ℕ) (i : Fin 2)
    (ν : Measure (StripConfiguration n)) : Prop :=
  IsProbabilityMeasure ν ∧
    ∀ (A : Finset (stripGraph n).edgeSet) (ξ : StripConfiguration n),
      Tendsto (fun m => stripWindowCylinderProbability θ n i m A ξ) atTop
        (𝓝 (ν.real {ω | ∀ e ∈ A, ω e = ξ e}))

/-- Every strip vertex lies in a window as soon as its horizontal coordinate
lies between the two window sides. -/
theorem mem_stripWindow_of_abs_fst_le (n m : ℕ) (v : stripVertices n)
    (hm : |v.1.1| ≤ (m : ℤ)) : v.1 ∈ stripWindow n m := by
  simp only [stripWindow, latticeRectangle, Finset.mem_product, Finset.mem_Icc]
  exact ⟨abs_le.mp hm, v.2⟩

/-- Strip windows exhaust every actual strip edge, with its original endpoints
and state carrier preserved by the finite edge lift. -/
theorem eventually_stripWindow_edge_lift (n : ℕ) (e : (stripGraph n).edgeSet) :
    ∀ᶠ m : ℕ in atTop,
      ∃ f : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    filter_upwards [eventually_ge_atTop (max u.1.1.natAbs v.1.1.natAbs)] with m hm
    have hu : u.1 ∈ stripWindow n m := by
      apply mem_stripWindow_of_abs_fst_le
      have h := le_trans (le_max_left _ _) hm
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    have hv : v.1 ∈ stripWindow n m := by
      apply mem_stripWindow_of_abs_fst_le
      have h := le_trans (le_max_right _ _) hm
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    let u' : (stripWindow n m : Set (ℤ × ℤ)) := ⟨u.1, hu⟩
    let v' : (stripWindow n m : Set (ℤ × ℤ)) := ⟨v.1, hv⟩
    have hadj : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).Adj u' v' :=
      (stripGraph n).mem_edgeSet.mp he
    refine ⟨⟨s(u', v'), (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).mem_edgeSet.mpr hadj⟩, ?_⟩
    rfl

/-- In particular, every finite pattern is eventually fully supported by the
window sequence used in the cylinder-limit definition. -/
theorem eventually_stripWindow_finset_edge_lift (n : ℕ)
    (A : Finset (stripGraph n).edgeSet) :
    ∀ᶠ m : ℕ in atTop, ∀ e ∈ A,
      ∃ f : (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))).edgeSet,
        Sym2.map Subtype.val f.1 = Sym2.map Subtype.val e.1 := by
  exact (eventually_all_finset A).mpr fun e _ => eventually_stripWindow_edge_lift n e

/-- A cylinder limit for a fixed lateral boundary convention is unique.
This does not assert that either convention converges or that their limits agree. -/
theorem isTopWiredStripLimit_unique (θ : PD.FK.Parameters) (n : ℕ) (i : Fin 2)
    (μ ν : Measure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n i μ) (hν : IsTopWiredStripLimit θ n i ν) : μ = ν := by
  let : IsProbabilityMeasure μ := hμ.1
  let : IsProbabilityMeasure ν := hν.1
  refine PD.ext_of_cylinders μ ν (fun _ => false) ?_
  intro A ξ
  have heq := tendsto_nhds_unique (hμ.2 A ξ) (hν.2 A ξ)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp heq

end PottsContinuity.RSW
