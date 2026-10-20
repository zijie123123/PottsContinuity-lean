module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActiveWindowLowerBound
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActiveRetainedPaths
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.StrictWindowSubwalk

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW
noncomputable section

/-- Every literal native-window crossing clips to an actual connection under
the active restriction. Boundary-column edges are removed by a subwalk. -/
theorem lemma4_native_window_crossing_restricts_to_active
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3)
    (C : Configuration (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A)))
    (hcross : (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4JointSourceReveal n A) C).val ∈
      primalWindowCrossing (box (56*n)) Set.univ ((10*(j:ℤ)-13)*(n:ℤ))
        ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ))) :
    embeddedConfigurationRestriction (lemma4ActiveNativeWindowGraph n A j)
      (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A))
      (lemma4ActiveNativeWindowEmbedding n A j) (lemma4ActiveNativeWindowGraph_map_le n A j) C ∈
        lemma4ActiveNativeWindowHorizontalCrossing n A j := by
  classical
  let G := lemma4AmbientGraph n
  let R := lemma4JointSourceReveal n A
  let H := edgeRestriction G R
  obtain ⟨u,v,p,hu,hv,hp⟩ := hcross
  have hgraph := openGraph_edgeRestriction G R C
  have hnative : ∀ d ∈ p.edges, d ∈ (openGraph H C).edgeSet := by
    intro d hd
    rw [hgraph]
    exact p.edges_subset_edgeSet hd
  let pN := p.transfer (openGraph H C) hnative
  have hpN : ∀ w ∈ pN.support,
      (10*(j:ℤ)-13)*(n:ℤ) ≤ w.val.1 ∧ w.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ) ∧
      -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ) := by
    intro w hw
    have hwp : w ∈ p.support := (SimpleGraph.Walk.support_transfer p hnative) ▸ hw
    exact (hp w hwp).2
  have hstep : ∀ x y, (openGraph H C).Adj x y → |x.val.1-y.val.1| ≤ 1 := by
    intro x y hxy
    have h := edgeRestriction_le G R (openGraph_le H C hxy)
    change |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 at h
    have := abs_nonneg (x.val.2-y.val.2)
    omega
  have hlr : (10*(j:ℤ)-13)*(n:ℤ) < (10*(j:ℤ)-7)*(n:ℤ) := by nlinarith
  obtain ⟨x,y,q,hsub,hx,hy,hslab,hnoboundary⟩ := walk_subwalk_between_levels_no_boundary_edges
    (fun w : (box (56*n) : Set LatticeVertex) => w.val.1) hstep pN hlr hu.le hv.ge
  have hedges : ∀ d ∈ q.edges, d ∈ (lemma4NativeWindowGraph n A j).edgeSet := by
    intro d hd
    induction hdval : d using Sym2.inductionOn with
    | hf s t =>
      rw [hdval] at hd
      have hs := hpN s (hsub.support_subset (q.fst_mem_support_of_mem_edges hd))
      have ht := hpN t (hsub.support_subset (q.snd_mem_support_of_mem_edges hd))
      apply (lemma4NativeWindowGraph n A j).mem_edgeSet.mpr
      exact ⟨openGraph_le H C (q.adj_of_mem_edges hd),hs,ht,
        (hnoboundary s t hd).1,(hnoboundary s t hd).2⟩
  have hxy : x ≠ y := by
    intro heq
    have hx' := congrArg (fun w : (box (56*n) : Set LatticeVertex) => w.val.1) heq
    omega
  obtain ⟨a,b,ha,hb,hconn⟩ := active_restriction_connection_of_retained_walk
    (lemma4NativeWindowGraph n A j) H (lemma4NativeWindowGraph_le n A j) C hxy q hedges
  refine ⟨a,b,?_,?_,hconn⟩
  · change a.val.val.1=(10*(j:ℤ)-13)*(n:ℤ)
    rw [ha]
    exact hx
  · change b.val.val.1=(10*(j:ℤ)-7)*(n:ℤ)
    rw [hb]
    exact hy

/-- Native noncrossing is implied by the active restriction noncrossing,
with no law, partition, selector, or restoration premise. -/
theorem lemma4_active_noncrossing_implies_native_noncrossing
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n)) (j : Fin 3)
    (C : Configuration (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A)))
    (hC : embeddedConfigurationRestriction (lemma4ActiveNativeWindowGraph n A j)
      (edgeRestriction (lemma4AmbientGraph n) (lemma4JointSourceReveal n A))
      (lemma4ActiveNativeWindowEmbedding n A j) (lemma4ActiveNativeWindowGraph_map_le n A j) C ∉
        lemma4ActiveNativeWindowHorizontalCrossing n A j) :
    C ∈ nativePrimalWindowNoncrossing (box (56*n)) (lemma4JointSourceReveal n A)
      ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)) := by
  intro hcross
  exact hC (lemma4_native_window_crossing_restricts_to_active n hn A j C hcross)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
