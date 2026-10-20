module

public import PottsContinuity.Thm1.ShellExitDependence
public import PottsContinuity.Thm1.ShellPairConnectivity
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import PottsContinuity.PD.CorrLength.ConnectionEvents

@[expose] public section

namespace PottsContinuity.Thm1

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.PD.CorrLength

noncomputable section

/-- The whole-lattice event that `x` reaches outside a finite vertex set. -/
def pottsESLatticeExitEventFrom (V : Finset (ℤ × ℤ)) (x : ℤ × ℤ) :
    Set LatticeConfiguration :=
  {ω | ∃ y, y ∉ V ∧ (PD.rcInfiniteOpenGraph ω).Reachable x y}

/-- The infinite-lattice form of the wired pair relation at a finite shell. -/
def pottsESLatticePairRelationEvent (V : Finset (ℤ × ℤ))
    (x y : ℤ × ℤ) : Set LatticeConfiguration :=
  {ω | (PD.rcInfiniteOpenGraph ω).Reachable x y ∨
    (ω ∈ pottsESLatticeExitEventFrom V x ∧
      ω ∈ pottsESLatticeExitEventFrom V y)}

private theorem pottsESOpenWalk_transfer
    (V : Finset (ℤ × ℤ)) {ω η : LatticeConfiguration}
    (hstates : ∀ e ∈ pottsESLatticeEdgeSet V, ω e = η e)
    {x y : ℤ × ℤ} (p : (PD.rcInfiniteOpenGraph ω).Walk x y)
    (hsupport : ∀ z, z ∈ p.support → z ∈ V) :
    (PD.rcInfiniteOpenGraph η).Reachable x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x z y hxy tail ih =>
    have hx : x ∈ V := hsupport x (by simp [SimpleGraph.Walk.support_cons])
    have hz : z ∈ V := hsupport z (by
      simpa only [SimpleGraph.Walk.support_cons] using
        (List.mem_cons_of_mem x (SimpleGraph.Walk.start_mem_support tail)))
    have htail : ∀ w, w ∈ tail.support → w ∈ V := by
      intro w hw
      exact hsupport w (List.mem_cons_of_mem _ hw)
    have hxy' := pottsESOpenAdj_transfer V hstates hx hxy
    exact hxy'.reachable.trans (ih htail)

private theorem pottsESLatticeExitEventFrom_dependsOn
    (V : Finset (ℤ × ℤ)) (x : ℤ × ℤ) (hx : x ∈ V) :
    DependsOn (pottsESLatticeEdgeSet V :
      Set PottsContinuity.PD.FK.squareLattice.edgeSet)
      (pottsESLatticeExitEventFrom V x) := by
  intro ω η hstates
  constructor
  · rintro ⟨y, hy, hreach⟩
    obtain ⟨p⟩ := hreach
    exact pottsESOpenWalk_exitTransfer V (fun e he => hstates e he) p hx hy
  · rintro ⟨y, hy, hreach⟩
    obtain ⟨p⟩ := hreach
    exact pottsESOpenWalk_exitTransfer V (fun e he => (hstates e he).symm) p hx hy

theorem pottsESLatticePairRelationEvent_dependsOn
    (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) (hx : x ∈ V) (hy : y ∈ V) :
    DependsOn (pottsESLatticeEdgeSet V :
      Set PottsContinuity.PD.FK.squareLattice.edgeSet)
      (pottsESLatticePairRelationEvent V x y) := by
  intro ω η hstates
  constructor
  · rintro (hpath | ⟨hExitX, hExitY⟩)
    · obtain ⟨p⟩ := hpath
      by_cases hinside : ∀ z, z ∈ p.support → z ∈ V
      · exact Or.inl (pottsESOpenWalk_transfer V hstates p hinside)
      · push Not at hinside
        obtain ⟨z, hzpath, hzoutside⟩ := hinside
        have hzReverse : z ∈ p.reverse.support := by
          simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzpath
        have hxExit := pottsESOpenWalk_exitTransfer V hstates
          (p.takeUntil z hzpath) hx hzoutside
        have hyExit := pottsESOpenWalk_exitTransfer V hstates
          (p.reverse.takeUntil z hzReverse) hy hzoutside
        exact Or.inr ⟨hxExit, hyExit⟩
    · exact Or.inr ⟨
        (pottsESLatticeExitEventFrom_dependsOn V x hx ω η hstates).mp hExitX,
        (pottsESLatticeExitEventFrom_dependsOn V y hy ω η hstates).mp hExitY⟩
  · rintro (hpath | ⟨hExitX, hExitY⟩)
    · obtain ⟨p⟩ := hpath
      by_cases hinside : ∀ z, z ∈ p.support → z ∈ V
      · exact Or.inl (pottsESOpenWalk_transfer V (fun e he => (hstates e he).symm) p hinside)
      · push Not at hinside
        obtain ⟨z, hzpath, hzoutside⟩ := hinside
        have hzReverse : z ∈ p.reverse.support := by
          simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzpath
        have hxExit := pottsESOpenWalk_exitTransfer V
          (fun e he => (hstates e he).symm) (p.takeUntil z hzpath) hx hzoutside
        have hyExit := pottsESOpenWalk_exitTransfer V
          (fun e he => (hstates e he).symm) (p.reverse.takeUntil z hzReverse) hy hzoutside
        exact Or.inr ⟨hxExit, hyExit⟩
    · exact Or.inr ⟨
        (pottsESLatticeExitEventFrom_dependsOn V x hx η ω
          (fun e he => (hstates e he).symm)).mp hExitX,
        (pottsESLatticeExitEventFrom_dependsOn V y hy η ω
          (fun e he => (hstates e he).symm)).mp hExitY⟩

theorem pottsESLatticePairRelationEvent_antitone {V W : Finset (ℤ × ℤ)}
    (hVW : V ⊆ W) (x y : ℤ × ℤ) :
    pottsESLatticePairRelationEvent W x y ⊆
      pottsESLatticePairRelationEvent V x y := by
  intro ω hω
  change (PD.rcInfiniteOpenGraph ω).Reachable x y ∨
    (ω ∈ pottsESLatticeExitEventFrom W x ∧
      ω ∈ pottsESLatticeExitEventFrom W y) at hω
  change (PD.rcInfiniteOpenGraph ω).Reachable x y ∨
    (ω ∈ pottsESLatticeExitEventFrom V x ∧
      ω ∈ pottsESLatticeExitEventFrom V y)
  rcases hω with hpath | ⟨hExitX, hExitY⟩
  · exact Or.inl hpath
  · rcases hExitX with ⟨z, hzW, hxReach⟩
    rcases hExitY with ⟨w, hwW, hyReach⟩
    exact Or.inr ⟨⟨z, fun hzV => hzW (hVW hzV), hxReach⟩,
      ⟨w, fun hwV => hwW (hVW hwV), hyReach⟩⟩

private theorem pottsESPairVolume_mono (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1)) : Monotone V := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact Finset.Subset.rfl
  | succ n ih =>
    by_cases hmn' : m ≤ n
    · exact (ih (by omega)).trans (hNest n)
    · have hm : m = n + 1 := by omega
      subst m
      exact Finset.Subset.rfl

private theorem pottsESPair_finite_subset_eventually
    (V : ℕ → Finset (ℤ × ℤ)) (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n) (F : Finset (ℤ × ℤ)) :
    ∃ n, F ⊆ V n := by
  have hMono := pottsESPairVolume_mono V hNest
  induction F using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert x F hx ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨n, hn⟩ := hExhaust x
    refine ⟨max m n, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hMono (Nat.le_max_right m n) hn
    · exact hMono (Nat.le_max_left m n) (hm hy)

theorem pottsESLatticePairRelationEvent_iInter_eq
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (x y : ℤ × ℤ) :
    (⋂ n, pottsESLatticePairRelationEvent (V n) x y) =
      {ω | (PD.rcInfiniteOpenGraph ω).Reachable x y ∨
        (ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y)} := by
  ext ω
  simp only [Set.mem_iInter, pottsESLatticePairRelationEvent, Set.mem_ofPred_eq]
  constructor
  · intro hω
    by_cases hxy : (PD.rcInfiniteOpenGraph ω).Reachable x y
    · exact Or.inl hxy
    · right
      have hxExit (n : ℕ) :
          ∃ w, w ∉ V n ∧ (PD.rcInfiniteOpenGraph ω).Reachable x w := by
        rcases hω n with hconn | ⟨hExitX, hExitY⟩
        · exact (hxy hconn).elim
        · exact hExitX
      have hyExit (n : ℕ) :
          ∃ w, w ∉ V n ∧ (PD.rcInfiniteOpenGraph ω).Reachable y w := by
        rcases hω n with hconn | ⟨hExitX, hExitY⟩
        · exact (hxy hconn).elim
        · exact hExitY
      have hinfinite (z : ℤ × ℤ) (hexit : ∀ n,
          ∃ w, w ∉ V n ∧ (PD.rcInfiniteOpenGraph ω).Reachable z w) :
          ω ∈ infiniteAt z := by
        apply (infinite_cluster_iff ω z).2
        intro F
        obtain ⟨n, hn⟩ := pottsESPair_finite_subset_eventually V hNest hExhaust F
        obtain ⟨w, hw, hreach⟩ := hexit n
        exact ⟨w, fun hwF => hw (hn hwF), hreach⟩
      exact ⟨hinfinite x hxExit, hinfinite y hyExit⟩
  · rintro (hxy | ⟨hxInf, hyInf⟩)
    · intro n
      exact Or.inl hxy
    · intro n
      have hxInfinite : (cluster ω x).Infinite := by
        simpa [infiniteAt] using hxInf
      have hyInfinite : (cluster ω y).Infinite := by
        simpa [infiniteAt] using hyInf
      obtain ⟨zx, hzx, hxReach⟩ :=
        (infinite_cluster_iff ω x).mp hxInfinite (V n)
      obtain ⟨zy, hzy, hyReach⟩ :=
        (infinite_cluster_iff ω y).mp hyInfinite (V n)
      exact Or.inr ⟨⟨zx, hzx, hxReach⟩, ⟨zy, hzy, hyReach⟩⟩

end

end PottsContinuity.Thm1
