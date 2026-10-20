module

public import PottsContinuity.Thm4Side.DeterministicReveals
public import PottsContinuity.Exploration.SourceTraceFiberOpen

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.PD.FK
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Exploration
open PottsContinuity.RSW

noncomputable section

local instance dominatedBallEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _

local instance dominatedBallEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

/-- The local root reveal records every source bond incident to the closed
max-norm ball used by the first-hit definition of the screen event. -/
noncomputable def slitScreenBallRevealEdges (m : ℕ) :
    PottsContinuity.PD.FK.Configuration (slitBoxGraph (16 * m)) := by
  classical
  exact Finset.univ.filter fun e =>
    ∀ v ∈ e.val, PottsContinuity.Thm4Side.slitScreenRadius m v ≤ (m : ℤ)

noncomputable def slitScreenBallReveal (m : ℕ) :
    RevealMap
      (G := slitBoxGraph (16 * m)) :=
  fun _ => slitScreenBallRevealEdges m

private theorem openAdj_transferred_of_ball_agreement
    (m : ℕ) (A B : PottsContinuity.PD.FK.Configuration
      (slitBoxGraph (16 * m)))
    (hagree : A ∩ slitScreenBallRevealEdges m =
      B ∩ slitScreenBallRevealEdges m)
    {u v : SlitBoxVertex (16 * m)}
    (hadj : (PottsContinuity.PD.FK.openGraph
      (slitBoxGraph (16 * m)) A).Adj u v)
    (hu : PottsContinuity.Thm4Side.slitScreenRadius m u ≤ (m : ℤ))
    (hv : PottsContinuity.Thm4Side.slitScreenRadius m v ≤ (m : ℤ)) :
    (PottsContinuity.PD.FK.openGraph
      (slitBoxGraph (16 * m)) B).Adj u v := by
  rcases (PottsContinuity.PD.FK.openGraph_adj _ _ _ _).mp hadj with
    ⟨e, heA, huv⟩
  have heR : e ∈ slitScreenBallRevealEdges m := by
    simp only [slitScreenBallRevealEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    intro z hz
    rw [huv] at hz
    rcases (Sym2.mem_iff').mp hz with hzu | hzv
    · rw [hzu]
      exact hu
    · rw [hzv]
      exact hv
  have hstate := Finset.ext_iff.mp hagree e
  simp only [Finset.mem_inter] at hstate
  have heB : e ∈ B := (hstate.mp ⟨heA, heR⟩).1
  exact (PottsContinuity.PD.FK.openGraph_adj _ _ _ _).mpr
    ⟨e, heB, huv⟩

private theorem screenWalk_transferred_of_ball_agreement
    (m : ℕ) (A B : PottsContinuity.PD.FK.Configuration
      (slitBoxGraph (16 * m)))
    (hagree : A ∩ slitScreenBallRevealEdges m =
      B ∩ slitScreenBallRevealEdges m)
    {u v : SlitBoxVertex (16 * m)}
    (p : (PottsContinuity.PD.FK.openGraph
      (slitBoxGraph (16 * m)) A).Walk u v)
    (hbound : ∀ z ∈ p.support,
      PottsContinuity.Thm4Side.slitScreenRadius m z ≤ (m : ℤ)) :
    ∃ p' : (PottsContinuity.PD.FK.openGraph
      (slitBoxGraph (16 * m)) B).Walk u v,
      p'.support = p.support := by
  have hstep : ∀ {x y}, s(x, y) ∈ p.edges →
      (PottsContinuity.PD.FK.openGraph
        (slitBoxGraph (16 * m)) B).Adj x y := by
    intro x y he
    have hx := hbound x (p.fst_mem_support_of_mem_edges he)
    have hy := hbound y (p.snd_mem_support_of_mem_edges he)
    exact openAdj_transferred_of_ball_agreement m A B hagree
      (p.adj_of_mem_edges he) hx hy
  exact openWalk_transfer_of_edgewise_adjacency
    (slitBoxGraph (16 * m)) A B p hstep

/-- The root connection event is determined by the local radius-m reveal. -/
theorem slitScreenEvent_iff_of_agree_ballReveal
    (m : ℕ) (A B : PottsContinuity.PD.FK.Configuration
      (slitBoxGraph (16 * m)))
    (hagree : A ∩ slitScreenBallRevealEdges m =
      B ∩ slitScreenBallRevealEdges m) :
    (A ∈ slitScreenEvent m ↔ B ∈ slitScreenEvent m) := by
  constructor
  · intro hA
    obtain ⟨z, hz, p, hp, hfirst, hbound⟩ :=
      PottsContinuity.Thm4Side.slitScreenEvent_firstHit_path_local m A hA
    refine ⟨z, hz, ?_⟩
    obtain ⟨p', _⟩ :=
      screenWalk_transferred_of_ball_agreement m A B hagree p hbound
    exact (PottsContinuity.PD.FK.actualConnected_iff_walk
      (slitBoxGraph (16 * m)) B
      (slitBoxBottomCenterVertex (16 * m)) z).mpr
      ⟨p'⟩
  · intro hB
    obtain ⟨z, hz, p, hp, hfirst, hbound⟩ :=
      PottsContinuity.Thm4Side.slitScreenEvent_firstHit_path_local m B hB
    refine ⟨z, hz, ?_⟩
    obtain ⟨p', _⟩ :=
      screenWalk_transferred_of_ball_agreement m B A hagree.symm p hbound
    exact (PottsContinuity.PD.FK.actualConnected_iff_walk
      (slitBoxGraph (16 * m)) A
      (slitBoxBottomCenterVertex (16 * m)) z).mpr
      ⟨p'⟩

end
end PottsContinuity.Thm4Plane
