-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/SurgeryEvents.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.ExteriorClusters
public import PottsContinuity.PD.RCInfinite.FiniteClusterExclusion
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- A possible open edge exit from a box, with its inner and outer endpoints. -/
abbrev BoxExit (n : ℕ) :=
  {d : BoxVertex (0, 0) n × BoxVertex (0, 0) (n + 1) //
    d.2.val ∉ latticeBox (0, 0) n ∧ squareLattice.Adj d.1.val d.2.val}

def boxExitInside {n : ℕ} (d : BoxExit n) : LatticeVertex := d.val.1.val

def boxExitOutside {n : ℕ} (d : BoxExit n) : LatticeVertex := d.val.2.val

def boxExitEdge {n : ℕ} (d : BoxExit n) : Edge :=
  ⟨s(boxExitInside d, boxExitOutside d),
    squareLattice.mem_edgeSet.mpr d.property.2⟩

theorem boxExit_outside_not_mem {n : ℕ} (d : BoxExit n) :
    boxExitOutside d ∉ latticeBox (0, 0) n := d.property.1

/-- The event that this prescribed box exit leads to an infinite exterior
component while remaining attached to its original cluster witness. -/
def boxExitWitnessEvent {n : ℕ} (x : LatticeVertex) (d : BoxExit n) :
    Set LatticeConfiguration :=
  {ω | ω (boxExitEdge d) = true ∧
    (rcInfiniteOpenGraph ω).Reachable x (boxExitOutside d) ∧
    ω ∈ exteriorInfiniteAt n (boxExitOutside d)}

theorem measurableSet_boxExitWitnessEvent {n : ℕ} (x : LatticeVertex) (d : BoxExit n) :
    MeasurableSet (boxExitWitnessEvent x d) := by
  exact ((isCylinder_coordinate (boxExitEdge d) true).measurableSet).inter
    ((measurableSet_open_reachable x (boxExitOutside d)).inter
      (measurableSet_exteriorInfiniteAt n (boxExitOutside d)))

theorem infiniteAt_has_boxExit (ω : LatticeConfiguration) (n : ℕ)
    (x : LatticeVertex) (hx : x ∈ latticeBox (0, 0) n)
    (hinf : ω ∈ infiniteAt x) :
    ∃ d : BoxExit n, ω ∈ boxExitWitnessEvent x d := by
  obtain ⟨inside, outside, he, hin, hout, hopen, hreach, hinfOutside⟩ :=
    infiniteAt_has_exterior_exit ω n x hx hinf
  have hadj : squareLattice.Adj inside outside := squareLattice.mem_edgeSet.mp he
  have houtNext : outside ∈ latticeBox (0, 0) (n + 1) := lattice_adj_box_succ hadj hin
  let d : BoxExit n :=
    ⟨(⟨inside, hin⟩, ⟨outside, houtNext⟩), hout, hadj⟩
  refine ⟨d, ?_⟩
  refine ⟨?_, hreach, hinfOutside⟩
  have hed : boxExitEdge d = ⟨s(inside, outside), he⟩ := by
    apply Subtype.ext
    rfl
  rw [hed]
  exact hopen

def boxExitTripleCell (n : ℕ) (xs : Fin 3 → LatticeVertex)
    (exits : Fin 3 → BoxExit n) : Set LatticeConfiguration :=
  infiniteClusterWitnesses xs ∩ ⋂ j, boxExitWitnessEvent (xs j) (exits j)

theorem measurableSet_boxExitTripleCell (n : ℕ) (xs : Fin 3 → LatticeVertex)
    (exits : Fin 3 → BoxExit n) : MeasurableSet (boxExitTripleCell n xs exits) := by
  unfold boxExitTripleCell
  exact (measurableSet_infiniteClusterWitnesses xs).inter
    (MeasurableSet.iInter fun j => measurableSet_boxExitWitnessEvent (xs j) (exits j))

/-- A positive-measure event of three specified infinite clusters contains a
positive-measure cell with one fixed exterior infinite branch for each cluster. -/
theorem exists_positive_boxExitTriple (μ : Measure LatticeConfiguration)
    [IsFiniteMeasure μ] (n : ℕ) (xs : Fin 3 → LatticeVertex)
    (hxsBox : ∀ j, xs j ∈ latticeBox (0, 0) n)
    (hpos : 0 < μ.real (infiniteClusterWitnesses xs)) :
    ∃ exits : Fin 3 → BoxExit n,
      0 < μ.real (boxExitTripleCell n xs exits) := by
  have hcover : infiniteClusterWitnesses xs ⊆
      ⋃ exits : Fin 3 → BoxExit n, boxExitTripleCell n xs exits := by
    intro ω hω
    have hexit (j : Fin 3) : ∃ d : BoxExit n, ω ∈ boxExitWitnessEvent (xs j) d :=
      infiniteAt_has_boxExit ω n (xs j) (hxsBox j) (hω.1 j)
    choose exits hexits using hexit
    refine mem_iUnion.mpr ⟨exits, ?_⟩
    exact ⟨hω, by simpa only [Set.mem_iInter] using hexits⟩
  by_contra hnone
  have hno (exits : Fin 3 → BoxExit n) :
      ¬ 0 < μ.real (boxExitTripleCell n xs exits) := by
    intro hposCell
    exact hnone ⟨exits, hposCell⟩
  have hzero (exits : Fin 3 → BoxExit n) :
      μ (boxExitTripleCell n xs exits) = 0 := by
    have hzreal : μ.real (boxExitTripleCell n xs exits) = 0 :=
      le_antisymm (not_lt.mp (hno exits)) measureReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp hzreal).resolve_right
      (measure_ne_top μ (boxExitTripleCell n xs exits))
  have hnull : μ (⋃ exits : Fin 3 → BoxExit n, boxExitTripleCell n xs exits) = 0 :=
    measure_iUnion_null hzero
  have hle : μ.real (infiniteClusterWitnesses xs) ≤ 0 := by
    calc
      μ.real (infiniteClusterWitnesses xs) ≤
          μ.real (⋃ exits : Fin 3 → BoxExit n, boxExitTripleCell n xs exits) :=
        measureReal_mono hcover
      _ = 0 := by simp [Measure.real, hnull]
  exact (not_lt_of_ge hle) hpos

/-- Some fixed witness tuple has positive measure whenever the three-cluster
threshold does. -/
theorem exists_positive_infiniteClusterWitnesses (μ : Measure LatticeConfiguration)
    [IsFiniteMeasure μ] (hpos : 0 < μ.real (atLeastInfiniteClusters 3)) :
    ∃ xs : Fin 3 → LatticeVertex,
      0 < μ.real (infiniteClusterWitnesses xs) := by
  have hEq : atLeastInfiniteClusters 3 =
      ⋃ xs : Fin 3 → LatticeVertex, infiniteClusterWitnesses xs := by
    ext ω
    simp [atLeastInfiniteClusters, infiniteClusterWitnesses]
  by_contra hnone
  have hno (xs : Fin 3 → LatticeVertex) :
      ¬ 0 < μ.real (infiniteClusterWitnesses xs) := by
    intro hposWitness
    exact hnone ⟨xs, hposWitness⟩
  have hzero (xs : Fin 3 → LatticeVertex) : μ (infiniteClusterWitnesses xs) = 0 := by
    have hzreal : μ.real (infiniteClusterWitnesses xs) = 0 :=
      le_antisymm (not_lt.mp (hno xs)) measureReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp hzreal).resolve_right
      (measure_ne_top μ (infiniteClusterWitnesses xs))
  have hnull : μ (⋃ xs : Fin 3 → LatticeVertex, infiniteClusterWitnesses xs) = 0 :=
    measure_iUnion_null hzero
  have hz : μ.real (atLeastInfiniteClusters 3) = 0 := by
    rw [hEq]
    simp [Measure.real, hnull]
  exact (not_lt_of_ge (le_of_eq hz)) hpos

theorem exists_box_containing_finset (S : Finset LatticeVertex) :
    ∃ n : ℕ, ∀ x ∈ S, x ∈ latticeBox (0, 0) n := by
  let f : LatticeVertex → ℕ := fun x => max x.1.natAbs x.2.natAbs
  let radius : ℕ := S.sup f
  refine ⟨radius, ?_⟩
  intro x hx
  rw [mem_latticeBox]
  have hmax : f x ≤ radius := by
    dsimp [radius]
    exact Finset.le_sup (f := f) hx
  have hfirst : (x.1.natAbs : ℤ) ≤ radius := by exact_mod_cast (le_trans (Nat.le_max_left _ _) hmax)
  have hsecond : (x.2.natAbs : ℤ) ≤ radius := by exact_mod_cast (le_trans (Nat.le_max_right _ _) hmax)
  rw [Int.natCast_natAbs] at hfirst hsecond
  rcases abs_le.mp hfirst with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hsecond with ⟨hylo, hyhi⟩
  simp only [zero_sub, zero_add]
  exact ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩

end
end PottsContinuity.PD.RCInfinite
