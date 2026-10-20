module

public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.ProductMeasure
public import PottsContinuity.Critical.WalkCounting
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace PottsContinuity.Critical

open PottsContinuity.PD.FK

noncomputable section

abbrev LatticeEdge := squareLattice.edgeSet

/-- A direction string represented by its actual lattice edges. -/
def walkCodeEdgeList (x : LatticeVertex) : List (Fin 4) → List LatticeEdge
  | [] => []
  | d :: ds =>
      (⟨s(x, latticeStep x d), squareLattice.mem_edgeSet.mpr (latticeStep_adj x d)⟩ :
        LatticeEdge) :: walkCodeEdgeList (latticeStep x d) ds

theorem walkCodeEdgeList_val (x : LatticeVertex) (ds : List (Fin 4)) :
    (walkCodeEdgeList x ds).map Subtype.val = walkCodeEdgesFrom x ds := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih => simp [walkCodeEdgeList, walkCodeEdgesFrom, ih]

theorem walkCodeEdgeList_length (x : LatticeVertex) (ds : List (Fin 4)) :
    (walkCodeEdgeList x ds).length = ds.length := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih => simp [walkCodeEdgeList, ih]

/-- The finite set of edges traversed by a direction code. -/
def walkCodeEdgeFinset {n : ℕ} (x : LatticeVertex) (c : WalkCode n) : Finset LatticeEdge :=
  (walkCodeEdgeList x c.toList).toFinset

theorem walkCodeEdgeList_val_ofWalk {x y : LatticeVertex}
    (p : squareLattice.Walk x y) :
    (walkCodeEdgeList x (walkCodeOfWalk p).toList).map Subtype.val = p.edges := by
  calc
    (walkCodeEdgeList x (walkCodeOfWalk p).toList).map Subtype.val =
        walkCodeEdgesFrom x (walkCodeOfWalk p).toList := walkCodeEdgeList_val _ _
    _ = p.edges := by simpa [walkCodeEdges] using walkCodeEdges_ofWalk p

theorem walkCodeEdgeList_nodup_of_path {x y : LatticeVertex}
    (p : squareLattice.Walk x y) (hp : p.IsPath) :
    (walkCodeEdgeList x (walkCodeOfWalk p).toList).Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [walkCodeEdgeList_val_ofWalk]
  exact hp.edges_nodup

/-- The cylinder event that all edges in a code are open. -/
def walkCodeOpenEvent {n : ℕ} (x : LatticeVertex) (c : WalkCode n) : Set (Set LatticeEdge) :=
  {S | (walkCodeEdgeFinset x c : Set LatticeEdge) ⊆ S}

/-- Direction codes whose traversed edge list has no repetitions. -/
def GoodWalkCode (x : LatticeVertex) (n : ℕ) :=
  {c : WalkCode n // (walkCodeEdgeList x c.toList).Nodup}

instance goodWalkCodeFintype (x : LatticeVertex) (n : ℕ) : Fintype (GoodWalkCode x n) := by
  classical
  unfold GoodWalkCode
  infer_instance

/-- The union of all-open cylinders over nonrepeating direction codes of length `n`. -/
def openWalkCodeUnion (x : LatticeVertex) (n : ℕ) : Set (Set LatticeEdge) :=
  ⋃ c : GoodWalkCode x n, walkCodeOpenEvent x c.1

/-- A walk event requiring every edge in its edge list to be open. -/
def walkOpenEvent {x y : LatticeVertex} (p : squareLattice.Walk x y) : Set (Set LatticeEdge) :=
  {S | ∀ e : LatticeEdge, e.val ∈ p.edges → e ∈ S}

/-- Some simple open walk of length `n` starts at `x`. -/
def openSimpleWalkEvent (x : LatticeVertex) (n : ℕ) : Set (Set LatticeEdge) :=
  {S | ∃ y, ∃ p : squareLattice.Walk x y,
    p.IsPath ∧ p.length = n ∧ S ∈ walkOpenEvent p}

theorem walkOpenEvent_subset_openWalkCodeUnion {x y : LatticeVertex}
    (p : squareLattice.Walk x y) (hp : p.IsPath) :
    walkOpenEvent p ⊆ openWalkCodeUnion x p.length := by
  intro S hS
  let c : GoodWalkCode x p.length :=
    ⟨walkCodeOfWalk p, walkCodeEdgeList_nodup_of_path p hp⟩
  refine Set.mem_iUnion.mpr ⟨c, ?_⟩
  change (walkCodeEdgeFinset x c.1 : Set LatticeEdge) ⊆ S
  intro e he
  change e ∈ (walkCodeEdgeList x c.1.toList).toFinset at he
  have heList : e ∈ walkCodeEdgeList x c.1.toList := List.mem_toFinset.mp he
  have heVal : e.val ∈ (walkCodeEdgeList x (walkCodeOfWalk p).toList).map Subtype.val :=
    List.mem_map.mpr ⟨e, heList, rfl⟩
  rw [walkCodeEdgeList_val_ofWalk] at heVal
  exact hS e heVal

theorem openSimpleWalkEvent_subset_openWalkCodeUnion (x : LatticeVertex) (n : ℕ) :
    openSimpleWalkEvent x n ⊆ openWalkCodeUnion x n := by
  intro S hS
  obtain ⟨y, p, hp, hlen, hopen⟩ := hS
  subst n
  exact walkOpenEvent_subset_openWalkCodeUnion p hp hopen

end
end PottsContinuity.Critical
