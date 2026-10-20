module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceBandQueryAvoidance
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.AnnulusWindowBoundary
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.StrictWindowSubwalk
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ResidualPrimalWindows
public import PottsContinuity.PlanarMixed.Lemma4Connectors.TraceIndexScreen

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality RSW Push
noncomputable section
local instance routeSevenTransportEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- Every actual between-loop crossing has a contiguous crossing on the
native residual. Band queries are outside its component; annulus queries
are removed by first/last-side clipping. -/
theorem lemma4_primal_window_crossing_has_native_residual_crossing
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n)
    {z : LatticeVertex} (P : PD.FK.squareLattice.Walk z z)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hstrip : ∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2 ∧ v.2 ≤ 3*(n:ℤ)-1)
    (j : Fin 3)
    (hcross : A ∈ primalWindowCrossing (box (56*n)) (traceIndexRegion (box (56*n)) P)
      ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ))) :
    A \ lemma4JointSourceReveal n A ∈ primalWindowCrossing (box (56*n)) Set.univ
      ((10*(j:ℤ)-13)*(n:ℤ)) ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ)) := by
  obtain ⟨u,v,p,hu,hv,hp⟩ := hcross
  let G := lemma4AmbientGraph n
  let R := lemma4JointSourceReveal n A
  have hstep : ∀ x y, (openGraph G A).Adj x y → |x.val.1-y.val.1| ≤ 1 := by
    intro x y hxy
    have h := openGraph_le G A hxy
    change |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 at h
    have := abs_nonneg (x.val.2-y.val.2)
    omega
  have hlr : (10*(j:ℤ)-13)*(n:ℤ) < (10*(j:ℤ)-7)*(n:ℤ) := by nlinarith
  obtain ⟨x,y,q,hsub,hx,hy,hslab,hnoboundary⟩ := walk_subwalk_between_levels_no_boundary_edges
    (fun w : (box (56*n) : Set LatticeVertex) => w.val.1) hstep p hlr hu.le hv.ge
  have hindex (w : (box (56*n) : Set LatticeVertex))
      (huw : ActualConnected _ A u w) : rayIndex w.val P=1 := by
    have hi : rayIndex u.val P=1 := (hp u p.start_mem_support).1
    have heq := rayIndex_eq_of_avoidance_reachable P
      (huw.map (finiteDualScreenOpenHom (box (56*n)) A P hclosed))
    change rayIndex u.val P=rayIndex w.val P at heq
    exact heq.symm.trans hi
  have hremain : ∀ d ∈ q.edges, d ∈ (openGraph G (A \ R)).edgeSet := by
    intro d hd
    induction hdval : d using Sym2.inductionOn with
    | hf s t =>
      rw [hdval] at hd
      have hadj := q.adj_of_mem_edges hd
      obtain ⟨e,he,heq⟩ := (openGraph_adj G A s t).mp hadj
      have hs : s ∈ q.support := q.fst_mem_support_of_mem_edges hd
      have ht : t ∈ q.support := q.snd_mem_support_of_mem_edges hd
      have hquery : e ∉ R := by
        intro heR
        change e ∈ lemma4AnnulusBondReveal n ∪ (lemma4SourceBandReveal n 0 A ∪ lemma4SourceBandReveal n 1 A) at heR
        rcases Finset.mem_union.mp heR with ha | hb
        · have hw : ∀ w ∈ e.val, (10*(j:ℤ)-13)*(n:ℤ) ≤ w.val.1 ∧
              w.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ) := by
            intro w hw
            rw [heq] at hw
            rcases Sym2.mem_iff'.mp hw with hw | hw
            · subst w; exact hslab s hs
            · subst w; exact hslab t ht
          rcases lemma4_annulus_query_in_window_boundary n j e ha hw with hleft | hright
          · have hl := hleft s (by rw [heq]; exact Sym2.mem_mk_left _ _)
            have hr := hleft t (by rw [heq]; exact Sym2.mem_mk_right _ _)
            exact (hnoboundary s t hd).1 ⟨hl,hr⟩
          · have hl := hright s (by rw [heq]; exact Sym2.mem_mk_left _ _)
            have hr := hright t (by rw [heq]; exact Sym2.mem_mk_right _ _)
            exact (hnoboundary s t hd).2 ⟨hl,hr⟩
        · have hroot : ActualConnected _ A u s := ⟨p.takeUntil s (hsub.support_subset hs)⟩
          exact lemma4_source_band_queries_avoid_component n hn A hA P hclosed hstrip u hindex e he
            ⟨s,by rw [heq]; exact Sym2.mem_mk_left _ _,hroot⟩ (by simpa only [Finset.mem_union] using hb)
      apply (openGraph G (A \ R)).mem_edgeSet.mpr
      exact (openGraph_adj G (A \ R) s t).mpr ⟨e,Finset.mem_sdiff.mpr ⟨he,hquery⟩,heq⟩
  let r := q.transfer (openGraph G (A \ R)) hremain
  refine ⟨x,y,r,hx,hy,?_⟩
  intro w hw
  have hwq : w ∈ q.support := (SimpleGraph.Walk.support_transfer q hremain) ▸ hw
  have hwp := hp w (hsub.support_subset hwq)
  exact ⟨Set.mem_univ _,(hslab w hwq).1,(hslab w hwq).2,hwp.2.2.2⟩

/-- Actual residual connectors imply the original between-loop noncrossings,
with no carrier, selector or query-geometry premise. -/
theorem lemma4_actual_residual_connectors_imply_trace_noncrossings
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n)
    {z : LatticeVertex} (P : PD.FK.squareLattice.Walk z z)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hstrip : ∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2 ∧ v.2 ≤ 3*(n:ℤ)-1)
    (hconnector : A ∈ lemma4ActualResidualConnectors n A) :
    A ∈ lemma4PrimalNoncrossings (box (56*n)) (traceIndexRegion (box (56*n)) P) n := by
  intro j hcross
  exact hconnector j (lemma4_primal_window_crossing_has_native_residual_crossing n hn A hA P hclosed hstrip j hcross)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
