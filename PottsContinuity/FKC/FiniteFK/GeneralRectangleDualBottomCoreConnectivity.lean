-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCoreConnectivity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreAmbientLaw
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomLeaves
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

local instance coreConnectivityEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (generalRectangleDualBottomCoreGraph a w h).edgeSet := Classical.decEq _
local instance coreConnectivityOuterEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _

def generalRectangleDualBottomCoreConfigurationRestriction (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h)) :
    Configuration (generalRectangleDualBottomCoreGraph a w h) :=
  embeddedConfigurationRestriction (generalRectangleDualBottomCoreGraph a w h)
    (rectangleDualGraph a w h) (generalRectangleDualBottomCoreInclusion a w h)
    (generalRectangleDualBottomCoreGraph_map_le a w h) A

/-- Each actual open dual edge either collapses under the bottom-leaf clamp,
or is an actual open edge of the retained induced core. -/
private theorem coreConnectivity_retraction_open_adj
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    {u v : RectangleDualVertex a w h}
    (huv : (openGraph (rectangleDualGraph a w h) A).Adj u v) :
    generalRectangleDualBottomCoreRetraction a w h u =
        generalRectangleDualBottomCoreRetraction a w h v ∨
      (openGraph (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestriction a w h A)).Adj
        (generalRectangleDualBottomCoreRetraction a w h u)
        (generalRectangleDualBottomCoreRetraction a w h v) := by
  classical
  let G := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleDualGraph a w h
  let f := generalRectangleDualBottomCoreInclusion a w h
  let r := generalRectangleDualBottomCoreRetraction a w h
  let R := generalRectangleDualBottomCoreConfigurationRestriction a w h A
  have hAdj : H.Adj u v := (openGraph_le H A) huv
  by_cases hurow : u.1.2 = a.2 - 1
  · obtain ⟨hcoords, _, _⟩ := generalRectangleDualBottomRow_adj_neighbor a w h
      u.1.1 u v (by exact Prod.ext rfl hurow) hAdj
    left
    apply Subtype.ext
    apply Subtype.ext
    simp [generalRectangleDualBottomCoreRetraction_val, hurow, hcoords]
  · by_cases hvrow : v.1.2 = a.2 - 1
    · obtain ⟨hcoords, _, _⟩ := generalRectangleDualBottomRow_adj_neighbor a w h
        v.1.1 v u (by exact Prod.ext rfl hvrow) hAdj.symm
      left
      apply Subtype.ext
      apply Subtype.ext
      simp [generalRectangleDualBottomCoreRetraction_val, hvrow, hcoords]
    · have huCore : a.2 ≤ u.1.2 := by
        have hx := u.2
        simp only [rectangleDualExpanded] at hx
        rw [mem_latticeRectangle] at hx
        omega
      have hvCore : a.2 ≤ v.1.2 := by
        have hx := v.2
        simp only [rectangleDualExpanded] at hx
        rw [mem_latticeRectangle] at hx
        omega
      let cu : generalRectangleDualBottomCoreVertex a w h := ⟨u, huCore⟩
      let cv : generalRectangleDualBottomCoreVertex a w h := ⟨v, hvCore⟩
      have hru : r u = cu := by
        apply Subtype.ext
        apply Subtype.ext
        simp [r, generalRectangleDualBottomCoreRetraction_val, cu, max_eq_left huCore]
      have hrv : r v = cv := by
        apply Subtype.ext
        apply Subtype.ext
        simp [r, generalRectangleDualBottomCoreRetraction_val, cv, max_eq_left hvCore]
      have hcoreAdj : G.Adj cu cv := by
        change H.Adj u v
        exact hAdj
      have hOpen : s(u, v) ∈ openEdges H A := (openGraph_adj H A u v).mp huv
      rcases hOpen with ⟨eH, heA, heval⟩
      let eG : G.edgeSet := ⟨s(cu, cv), G.mem_edgeSet.mpr hcoreAdj⟩
      have hstate : eG ∈ R := by
        change eG ∈ embeddedConfigurationRestriction G H f
          (generalRectangleDualBottomCoreGraph_map_le a w h) A
        rw [mem_embeddedConfigurationRestriction]
        have hmap : embeddedEdgeEmbedding G H f (generalRectangleDualBottomCoreGraph_map_le a w h) eG = eH := by
          apply Subtype.ext
          rw [embeddedEdgeEmbedding_coe, Function.Embedding.sym2Map_apply, Sym2.map_mk]
          rw [heval]
          simp [f, generalRectangleDualBottomCoreInclusion, cu, cv]
        exact hmap ▸ heA
      right
      change (openGraph G R).Adj (r u) (r v)
      rw [hru, hrv, openGraph_adj]
      exact ⟨eG, hstate, rfl⟩

/-- Every actual open edge in the restricted core lifts to an actual open
edge of the full true-dual graph. -/
private theorem coreConnectivity_lift_open_adj
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    {u v : generalRectangleDualBottomCoreVertex a w h}
    (huv : (openGraph (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestriction a w h A)).Adj u v) :
    (openGraph (rectangleDualGraph a w h) A).Adj
      (generalRectangleDualBottomCoreInclusion a w h u)
      (generalRectangleDualBottomCoreInclusion a w h v) := by
  classical
  let G := generalRectangleDualBottomCoreGraph a w h
  let H := rectangleDualGraph a w h
  let f := generalRectangleDualBottomCoreInclusion a w h
  let R := generalRectangleDualBottomCoreConfigurationRestriction a w h A
  rw [openGraph_adj] at huv ⊢
  rcases huv with ⟨eG, heR, heuv⟩
  refine ⟨embeddedEdgeEmbedding G H f (generalRectangleDualBottomCoreGraph_map_le a w h) eG,
    ?_, ?_⟩
  · exact (mem_embeddedConfigurationRestriction G H f
      (generalRectangleDualBottomCoreGraph_map_le a w h) A eG).mp heR
  · rw [embeddedEdgeEmbedding_coe]
    change Sym2.map f eG.val = s(f u, f v)
    rw [heuv, Sym2.map_mk]

/-- Induction on the actual walk turns the edgewise clamp alternatives into
actual connectivity; collapsed leaf excursions become reflexive steps. -/
private theorem coreConnectivity_retraction_walk
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    {u v : RectangleDualVertex a w h}
    (p : (openGraph (rectangleDualGraph a w h) A).Walk u v) :
    ActualConnected (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestriction a w h A)
      (generalRectangleDualBottomCoreRetraction a w h u)
      (generalRectangleDualBottomCoreRetraction a w h v) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hadj tail ih =>
      rcases coreConnectivity_retraction_open_adj a w h A hadj with heq | hcore
      · rw [heq]
        exact ih
      · exact (actualConnected_of_adj _ _ hcore).trans ih

/-- A core walk lifts edge by edge because restriction reads exactly the
original ambient edge state. -/
private theorem coreConnectivity_lift_walk
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    {u v : generalRectangleDualBottomCoreVertex a w h}
    (p : (openGraph (generalRectangleDualBottomCoreGraph a w h)
      (generalRectangleDualBottomCoreConfigurationRestriction a w h A)).Walk u v) :
    Nonempty ((openGraph (rectangleDualGraph a w h) A).Walk
      (generalRectangleDualBottomCoreInclusion a w h u)
      (generalRectangleDualBottomCoreInclusion a w h v)) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons x y z hadj tail ih =>
      rcases ih with ⟨q⟩
      exact ⟨SimpleGraph.Walk.cons
        (coreConnectivity_lift_open_adj a w h A hadj) q⟩

/-- Actual connectivity between retained vertices is unchanged by deleting
only the free bottom leaves. -/
theorem generalRectangleDualBottomCore_actualConnected_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    (u v : generalRectangleDualBottomCoreVertex a w h) :
    ActualConnected (rectangleDualGraph a w h) A
        (generalRectangleDualBottomCoreInclusion a w h u)
        (generalRectangleDualBottomCoreInclusion a w h v) ↔
      ActualConnected (generalRectangleDualBottomCoreGraph a w h)
        (generalRectangleDualBottomCoreConfigurationRestriction a w h A) u v := by
  constructor
  · intro hconn
    rcases (actualConnected_iff_walk _ _ _ _).mp hconn with ⟨p⟩
    have hcore := coreConnectivity_retraction_walk a w h A p
    simpa using hcore
  · intro hconn
    rcases (actualConnected_iff_walk _ _ _ _).mp hconn with ⟨p⟩
    exact (actualConnected_iff_walk _ _ _ _).mpr
      (coreConnectivity_lift_walk a w h A p)

private theorem generalRectangleDualBottomCoreRetraction_mem_threeSides
    (a : LatticeVertex) (w h : ℕ) (v : RectangleDualVertex a w h)
    (hv : v ∈ generalRectangleDualBottomCollarInnerThreeSides a w h) :
    generalRectangleDualBottomCoreInclusion a w h
      (generalRectangleDualBottomCoreRetraction a w h v) ∈
        generalRectangleDualBottomCollarInnerThreeSides a w h := by
  simp only [generalRectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq] at hv ⊢
  rcases hv with hleft | hright | htop
  · exact Or.inl hleft
  · exact Or.inr (Or.inl hright)
  · exact Or.inr (Or.inr (by
      simp [generalRectangleDualBottomCoreInclusion,
        generalRectangleDualBottomCoreRetraction_val, htop,
        ]))

/-- A path from a retained vertex to any of the full left, right, or top
boundary sides is equivalent to a path to the retained three-side boundary.
In particular the removed bottom corners are handled by the actual clamp. -/
theorem generalRectangleDualBottomCore_connected_to_fullThreeSides_iff
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleDualGraph a w h))
    (u : generalRectangleDualBottomCoreVertex a w h) :
    (∃ v : RectangleDualVertex a w h,
      v ∈ generalRectangleDualBottomCollarInnerThreeSides a w h ∧
      ActualConnected (rectangleDualGraph a w h) A
        (generalRectangleDualBottomCoreInclusion a w h u) v) ↔
    (∃ v : generalRectangleDualBottomCoreVertex a w h,
      generalRectangleDualBottomCoreInclusion a w h v ∈
        generalRectangleDualBottomCollarInnerThreeSides a w h ∧
      ActualConnected (generalRectangleDualBottomCoreGraph a w h)
        (generalRectangleDualBottomCoreConfigurationRestriction a w h A) u v) := by
  constructor
  · rintro ⟨v, hv, hconn⟩
    rcases (actualConnected_iff_walk _ _ _ _).mp hconn with ⟨p⟩
    have hcore := coreConnectivity_retraction_walk a w h A p
    refine ⟨generalRectangleDualBottomCoreRetraction a w h v,
      generalRectangleDualBottomCoreRetraction_mem_threeSides a w h v hv, ?_⟩
    simpa using hcore
  · rintro ⟨v, hv, hconn⟩
    exact ⟨generalRectangleDualBottomCoreInclusion a w h v, hv,
      (generalRectangleDualBottomCore_actualConnected_iff a w h A u v).mpr hconn⟩

end
end PottsContinuity.FKC.FiniteFK
