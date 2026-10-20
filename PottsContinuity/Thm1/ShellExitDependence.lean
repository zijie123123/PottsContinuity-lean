module

public import PottsContinuity.Thm1.ShellPathBridge
public import PottsContinuity.Thm1.ShellBoxComparison
public import PottsContinuity.PD.RCInfinite.Cylinders

@[expose] public section

namespace PottsContinuity.Thm1

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

 theorem pottsESOriginalEdge_mem {V : Finset (ℤ × ℤ)}
    {e : Sym2 (ℤ × ℤ)} (he : e ∈ pottsEdges V) :
    e ∈ PottsContinuity.PD.FK.squareLattice.edgeSet := by
  induction e using Sym2.ind with
  | _ x y =>
    have hx : x ∈ (s(x, y) : Sym2 (ℤ × ℤ)) := by simp
    have hy : y ∈ (s(x, y) : Sym2 (ℤ × ℤ)) := by simp
    have he' : s(x, y) ∈ pottsEdges V := by simpa using he
    have hne : x ≠ y := by
      intro heq
      subst y
      have hdiag : (s(x, x) : Sym2 (ℤ × ℤ)).IsDiag := by simp
      exact pottsEdges_not_diag V he' hdiag
    exact PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mpr
      (pottsEdges_endpoints_adjacent he' hx hy hne)

def pottsESOriginalEdgeEmbedding (V : Finset (ℤ × ℤ)) :
    pottsEdges V ↪ PottsContinuity.PD.FK.squareLattice.edgeSet where
  toFun := fun e => ⟨e.1, pottsESOriginalEdge_mem e.2⟩
  inj' := by
    intro e f h
    apply Subtype.ext
    exact congrArg (fun z : PottsContinuity.PD.FK.squareLattice.edgeSet => z.1) h

/-- The finite set of lattice bonds in the Edwards--Sokal shell graph. -/
def pottsESLatticeEdgeSet (V : Finset (ℤ × ℤ)) :
    Finset PottsContinuity.PD.FK.squareLattice.edgeSet :=
  Finset.univ.map (pottsESOriginalEdgeEmbedding V)

theorem pottsESLatticeEdgeSet_mem_iff (V : Finset (ℤ × ℤ))
    (e : PottsContinuity.PD.FK.squareLattice.edgeSet) :
    e ∈ pottsESLatticeEdgeSet V ↔ ∃ f : pottsEdges V, f.1 = e.1 := by
  constructor
  · intro he
    unfold pottsESLatticeEdgeSet at he
    obtain ⟨f, _, hfe⟩ := Finset.mem_map.mp he
    refine ⟨f, ?_⟩
    exact congrArg Subtype.val hfe
  · rintro ⟨f, hf⟩
    unfold pottsESLatticeEdgeSet
    apply Finset.mem_map.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact hf

theorem pottsESOpenAdj_transfer
    (V : Finset (ℤ × ℤ)) {ω η : LatticeConfiguration}
    (hstates : ∀ e ∈ pottsESLatticeEdgeSet V, ω e = η e)
    {x y : ℤ × ℤ} (hx : x ∈ V)
    (hxy : (PD.rcInfiniteOpenGraph ω).Adj x y) :
    (PD.rcInfiniteOpenGraph η).Adj x y := by
  obtain ⟨hedge, hopen⟩ := (rcInfiniteOpenGraph_adj ω x y).mp hxy
  let e : PottsContinuity.PD.FK.squareLattice.edgeSet := ⟨s(x, y), hedge⟩
  have hpotts : s(x, y) ∈ pottsEdges V :=
    pottsEdges_contains_adjacent_pair hx
      (PottsContinuity.PD.FK.squareLattice.mem_edgeSet.mp hedge)
  have hmem : e ∈ pottsESLatticeEdgeSet V := by
    unfold pottsESLatticeEdgeSet
    apply Finset.mem_map.mpr
    refine ⟨⟨e.1, hpotts⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    rfl
  have hη : η e = true := by
    rw [← hstates e hmem]
    exact hopen
  exact (rcInfiniteOpenGraph_adj η x y).mpr ⟨hedge, hη⟩

theorem pottsESOpenWalk_exitTransfer
    (V : Finset (ℤ × ℤ)) {ω η : LatticeConfiguration}
    (hstates : ∀ e ∈ pottsESLatticeEdgeSet V, ω e = η e)
    {x y : ℤ × ℤ} (w : (PD.rcInfiniteOpenGraph ω).Walk x y)
    (hx : x ∈ V) (hy : y ∉ V) :
    ∃ z, z ∉ V ∧ (PD.rcInfiniteOpenGraph η).Reachable x z := by
  induction w with
  | nil => exact False.elim (hy hx)
  | @cons x z y hxy tail ih =>
    have hxyη := pottsESOpenAdj_transfer V hstates hx hxy
    by_cases hz : z ∈ V
    · obtain ⟨w, hw, hreach⟩ := ih hz hy
      exact ⟨w, hw, hxyη.reachable.trans hreach⟩
    · exact ⟨z, hz, hxyη.reachable⟩

/-- Origin reachability to the exterior of a finite set reads only the edges
that meet that set. -/
def pottsESLatticeExitEvent (V : Finset (ℤ × ℤ)) : Set LatticeConfiguration :=
  {ω | ∃ y, y ∉ V ∧ (PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y}

theorem pottsESLatticeExitEvent_dependsOn
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V) :
    DependsOn (pottsESLatticeEdgeSet V :
      Set PottsContinuity.PD.FK.squareLattice.edgeSet)
      (pottsESLatticeExitEvent V) := by
  intro ω η hω
  constructor
  · rintro ⟨y, hy, hpath⟩
    obtain ⟨z, hz, hreach⟩ := hpath.elim fun w =>
      pottsESOpenWalk_exitTransfer V (fun e he => hω e he) w h0 hy
    exact ⟨z, hz, hreach⟩
  · rintro ⟨y, hy, hpath⟩
    obtain ⟨z, hz, hreach⟩ := hpath.elim fun w =>
      pottsESOpenWalk_exitTransfer V (fun e he => (hω e he).symm) w h0 hy
    exact ⟨z, hz, hreach⟩

theorem pottsESLatticeExitEvent_isCylinder
    (V : Finset (ℤ × ℤ)) (h0 : (0, 0) ∈ V) :
    IsCylinder (pottsESLatticeExitEvent V) :=
  ⟨pottsESLatticeEdgeSet V, pottsESLatticeExitEvent_dependsOn V h0⟩

end

end PottsContinuity.Thm1
