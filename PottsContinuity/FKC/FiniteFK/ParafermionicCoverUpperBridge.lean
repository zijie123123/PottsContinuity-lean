-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverUpperBridge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverWalk
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRectangleBoundary
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalk
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC


noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance bridgeAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance bridgeAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _
local instance bridgeStripEdgeFintype (n : ℕ) :
    Fintype (ParafermionicStripGraph n).edgeSet := Fintype.ofFinite _
local instance bridgeStripEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicStripGraph n).edgeSet := Classical.decEq _

def upperSheetVertices (n : ℕ) (k : ℤ) : Set (ParafermionicAmbientVertex n) :=
  {z | (z.1 : ParafermionicCoverVertex).2 = k ∧
    0 ≤ (z.1 : ParafermionicCoverVertex).1.2}

def upperStripMap (n : ℕ) (k : ℤ)
    (_hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (z : upperSheetVertices n k) : ParafermionicStripVertex n := by
  refine ⟨(z.1 : ParafermionicCoverVertex).1, ?_⟩
  rcases (parafermionicCoverBoxVertices_mem n (z.1 : ParafermionicCoverVertex)).mp z.1.2 with h
  rcases h with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi⟩
  have hypos : 0 ≤ (z.1 : ParafermionicCoverVertex).1.2 := z.2.2
  rw [mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

private theorem upperStripMap_lift (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (z : upperSheetVertices n k) :
    parafermionicCoverStripEmbedding n k hk (upperStripMap n k hk z) = z.1 := by
  apply Subtype.ext
  change ((upperStripMap n k hk z).1, k) = (z.1 : ParafermionicCoverVertex)
  apply Prod.ext
  · rfl
  · exact z.2.1.symm

def coverBase {n : ℕ} (z : ParafermionicAmbientVertex n) : LatticeVertex :=
  (z : ParafermionicCoverVertex).1

def coverSheet {n : ℕ} (z : ParafermionicAmbientVertex n) : ℤ :=
  (z : ParafermionicCoverVertex).2

private theorem coverAdj_of_openAdj (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (h : (openGraph (ParafermionicAmbientGraph n) A).Adj u v) :
  parafermionicCoverGraph.Adj (u : ParafermionicCoverVertex)
      (v : ParafermionicCoverVertex) :=
  (parafermionicCoverBoxInclusionHom n).map_rel' (openGraph_le _ _ h)

def upperSheetOpenGraphHom (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (openGraph (ParafermionicAmbientGraph n) A).induce (upperSheetVertices n k) →g
      openGraph (ParafermionicStripGraph n)
        (embeddedConfigurationRestriction (ParafermionicStripGraph n)
          (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
          (parafermionicCoverStrip_map_le n k hk) A) where
  toFun z := upperStripMap n k hk z
  map_rel' := by
    intro u v huv
    have hopen : (openGraph (ParafermionicAmbientGraph n) A).Adj u.1 v.1 := by
      refine ⟨huv.1, ?_⟩
      intro heq
      apply huv.2
      exact heq
    have hopen' := (openGraph_adj _ _ _ _).mp hopen
    rcases hopen' with ⟨e, heA, heval⟩
    have hbox : (ParafermionicAmbientGraph n).Adj u.1 v.1 := openGraph_le _ _ hopen
    have hbase : squareLattice.Adj
        (upperStripMap n k hk u).1 (upperStripMap n k hk v).1 := by
      simpa [upperStripMap] using hbox.1
    have hstrip : (ParafermionicStripGraph n).Adj
        (upperStripMap n k hk u) (upperStripMap n k hk v) :=
      (rectangleGraph_adj_iff (-(n:ℤ),0) (2*n) n _ _).2 hbase
    let e' : (ParafermionicStripGraph n).edgeSet := ⟨s(upperStripMap n k hk u,
      upperStripMap n k hk v), (ParafermionicStripGraph n).mem_edgeSet.mpr hstrip⟩
    have hmap : embeddedEdgeEmbedding (ParafermionicStripGraph n)
        (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
        (parafermionicCoverStrip_map_le n k hk) e' = e := by
      apply Subtype.ext
      rw [embeddedEdgeEmbedding_coe]
      change s(parafermionicCoverStripEmbedding n k hk (upperStripMap n k hk u),
        parafermionicCoverStripEmbedding n k hk (upperStripMap n k hk v)) = e.val
      rw [upperStripMap_lift n k hk u, upperStripMap_lift n k hk v, heval]
    have he' : e' ∈ embeddedConfigurationRestriction (ParafermionicStripGraph n)
        (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
        (parafermionicCoverStrip_map_le n k hk) A := by
      rw [mem_embeddedConfigurationRestriction]
      rw [hmap]
      exact heA
    apply (openGraph_adj _ _ _ _).2
    rw [openEdges]
    exact ⟨e', he', rfl⟩

theorem parafermionicCoverUpperBridge
    (n : ℕ) (_hn : 1 ≤ n) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (A : Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicAmbientVertex n)
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (huX : 1 ≤ u.val.1.1) (huY : u.val.1.2 < 0)
    (hvX : v.val.1.1 ≤ 0) (hvY : v.val.1.2 < 0)
    (hsheet : ∀ z ∈ w.support, z.val.2 = k) :
    ∃ s t : ParafermionicStripVertex n,
      s.1.2 = 0 ∧ t.1.2 = 0 ∧ 1 ≤ s.1.1 ∧ t.1.1 ≤ 0 ∧
      ActualConnected (ParafermionicStripGraph n)
        (embeddedConfigurationRestriction (ParafermionicStripGraph n)
          (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
          (parafermionicCoverStrip_map_le n k hk) A) s t := by
  classical
  have huX' : 1 ≤ (coverBase u).1 := by simpa [coverBase] using huX
  have huY' : (coverBase u).2 < 0 := by simpa [coverBase] using huY
  have hvX' : (coverBase v).1 ≤ 0 := by simpa [coverBase] using hvX
  have hvY' : (coverBase v).2 < 0 := by simpa [coverBase] using hvY
  let leftLower (i : ℕ) : Prop :=
    (coverBase (w.getVert i)).1 ≤ 0 ∧ (coverBase (w.getVert i)).2 < 0
  let rightLower (i : ℕ) : Prop :=
    1 ≤ (coverBase (w.getVert i)).1 ∧ (coverBase (w.getVert i)).2 < 0
  let leftIndices := (Finset.range (w.length + 1)).filter leftLower
  have hleftNe : leftIndices.Nonempty := by
    refine ⟨w.length, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    simpa [leftLower, w.getVert_length] using And.intro hvX' hvY'
  let i := leftIndices.min' hleftNe
  have hiLeft : leftLower i := (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
  have hiBound : i < w.length + 1 := Finset.mem_range.mp
    (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
  have hiLe : i ≤ w.length := by omega
  have hfirst : ∀ t, t < i → ¬ leftLower t := by
    intro t hti htl
    have htMem : t ∈ leftIndices := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), htl⟩
    have hmin := Finset.min'_le leftIndices t htMem
    omega
  have hipos : 0 < i := by
    by_contra hnot
    have hizero : i = 0 := by omega
    have h := hiLeft.1
    change (coverBase (w.getVert i)).1 ≤ 0 at h
    rw [hizero, w.getVert_zero] at h
    omega
  let rightIndices := (Finset.range i).filter rightLower
  have hrightNe : rightIndices.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hipos, ?_⟩⟩
    simpa [rightLower, w.getVert_zero] using And.intro huX' huY'
  let j := rightIndices.max' hrightNe
  have hjRight : rightLower j := (Finset.mem_filter.mp (Finset.max'_mem _ _)).2
  have hjLt : j < i := Finset.mem_range.mp
    (Finset.mem_filter.mp (Finset.max'_mem _ _)).1
  have hlast : ∀ t, j < t → t < i → ¬ rightLower t := by
    intro t hjt hti htr
    have htMem : t ∈ rightIndices := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hti, htr⟩
    have hmax := Finset.le_max' rightIndices t htMem
    omega
  have hgap : j + 1 < i := by
    by_contra hnot
    have hEq : j + 1 = i := by omega
    have hadj := w.adj_getVert_succ (by omega : j < w.length)
    have hbox := coverAdj_of_openAdj n A hadj
    have hxyj := hjRight.1
    have hyyj := hjRight.2
    have hxyi := hiLeft.1
    have hyyi := hiLeft.2
    have hsJ : coverSheet (w.getVert j) = k := by
      apply hsheet
      exact w.getVert_mem_support j
    have hsI : coverSheet (w.getVert i) = k := by
      apply hsheet
      exact w.getVert_mem_support i
    simp only [coverSheet] at hsJ hsI
    have hcases := (parafermionicCoverGraph_adj_iff_cases _ _).mp hbox
    rw [hEq] at hcases
    unfold parafermionicCoverAdjCases at hcases
    rcases hcases with h | h | h | h | h | h | h | h <;>
      simp only [coverBase] at h hxyj hyyj hxyi hyyi hsJ hsI <;> omega
  have hleftUpper : ∀ t, j + 1 ≤ t → t ≤ i - 1 →
      0 ≤ (coverBase (w.getVert t)).2 := by
    intro t hjt hti
    by_contra hneg
    have hty : (coverBase (w.getVert t)).2 < 0 := by omega
    by_cases htx : (coverBase (w.getVert t)).1 ≤ 0
    · exact hfirst t (by omega) ⟨htx, hty⟩
    · have htx' : 1 ≤ (coverBase (w.getVert t)).1 := by omega
      have htm : t ∈ rightIndices := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), ⟨htx', hty⟩⟩
      have hmax := Finset.le_max' rightIndices t htm
      omega
  have hq0y : (coverBase (w.getVert (j + 1))).2 = 0 := by
    have hnotLower : ¬ leftLower (j+1) ∧ ¬ rightLower (j+1) := by
      constructor
      · exact hfirst _ (by omega)
      · exact hlast _ (by omega) (by omega)
    have hadj := w.adj_getVert_succ (by omega : j < w.length)
    have hcoords := (coverAdj_of_openAdj n A hadj).1
    change squareLattice.Adj (coverBase (w.getVert j))
      (coverBase (w.getVert (j+1))) at hcoords
    rw [squareLattice_adj_iff] at hcoords
    have hnextnonneg : 0 ≤ (coverBase (w.getVert (j+1))).2 := by
      by_contra hnneg
      have hneg : (coverBase (w.getVert (j+1))).2 < 0 := by omega
      rcases hnotLower with ⟨hL,hR⟩
      by_cases hx : (coverBase (w.getVert (j+1))).1 ≤ 0
      · exact hL ⟨hx,hneg⟩
      · exact hR ⟨by omega,hneg⟩
    have hyj := hjRight.2
    rcases hcoords with hor | ver
    · rcases hor with ⟨hx | hx, hy⟩ <;> omega
    · rcases ver.2 with hy | hy <;> omega
  have hq0x : 1 ≤ (coverBase (w.getVert (j + 1))).1 := by
    have hadj := w.adj_getVert_succ (by omega : j < w.length)
    have hcoords := (coverAdj_of_openAdj n A hadj).1
    change squareLattice.Adj (coverBase (w.getVert j))
      (coverBase (w.getVert (j+1))) at hcoords
    rw [squareLattice_adj_iff] at hcoords
    rcases hcoords with hor | ver
    · rcases hor with ⟨hx | hx, hy⟩ <;> omega
    · rcases ver.2 with hy | hy <;> omega
  have hq1y : (coverBase (w.getVert (i - 1))).2 = 0 := by
    have hnotLower : ¬ leftLower (i-1) ∧ ¬ rightLower (i-1) := by
      constructor
      · exact hfirst _ (by omega)
      · exact hlast _ (by omega) (by omega)
    have hadj := w.adj_getVert_succ (by omega : i - 1 < w.length)
    have hcoords := (coverAdj_of_openAdj n A hadj).1
    have hid : i - 1 + 1 = i := by omega
    rw [hid] at hcoords
    change squareLattice.Adj (coverBase (w.getVert (i-1)))
      (coverBase (w.getVert i)) at hcoords
    rw [squareLattice_adj_iff] at hcoords
    have hprevnonneg : 0 ≤ (coverBase (w.getVert (i-1))).2 := by
      by_contra hnneg
      have hneg : (coverBase (w.getVert (i-1))).2 < 0 := by omega
      rcases hnotLower with ⟨hL,hR⟩
      by_cases hx : (coverBase (w.getVert (i-1))).1 ≤ 0
      · exact hL ⟨hx,hneg⟩
      · exact hR ⟨by omega,hneg⟩
    have hyi := hiLeft.2
    rcases hcoords with hor | ver
    · rcases hor with ⟨hx | hx, hy⟩ <;> omega
    · rcases ver.2 with hy | hy <;> omega
  have hq1x : (coverBase (w.getVert (i-1))).1 ≤ 0 := by
    have hadj := w.adj_getVert_succ (by omega : i - 1 < w.length)
    have hcoords := (coverAdj_of_openAdj n A hadj).1
    have hid : i - 1 + 1 = i := by omega
    rw [hid] at hcoords
    change squareLattice.Adj (coverBase (w.getVert (i-1)))
      (coverBase (w.getVert i)) at hcoords
    rw [squareLattice_adj_iff] at hcoords
    rcases hcoords with hor | ver
    · rcases hor with ⟨hx | hx, hy⟩ <;> omega
    · rcases ver.2 with hy | hy <;> omega
  let q := (w.drop (j+1)).take (i-j-2)
  have hqLength : q.length = i-j-2 := by
    simp [q, SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
    omega
  have hqEnd : (w.drop (j+1)).getVert (i-j-2) = w.getVert (i-1) := by
    rw [SimpleGraph.Walk.drop_getVert]
    congr 1; omega
  have hqSupport : ∀ z ∈ q.support, z ∈ upperSheetVertices n k := by
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp hz with ⟨t, hzt, ht⟩
    have ht' : t ≤ i-j-2 := by simpa [hqLength] using ht
    have hget : q.getVert t = w.getVert (j+1+t) := by
      change ((w.drop (j+1)).take (i-j-2)).getVert t = _
      rw [SimpleGraph.Walk.take_getVert, SimpleGraph.Walk.drop_getVert]
      congr 1
      omega
    have hpos : j+1 ≤ j+1+t := by omega
    have hbound : j+1+t ≤ i-1 := by omega
    have hY := hleftUpper (j+1+t) hpos hbound
    have hsh : coverSheet (w.getVert (j+1+t)) = k := by
      apply hsheet
      exact w.getVert_mem_support (j+1+t)
    have hY' : 0 ≤ (coverBase z).2 := by
      rw [← hget] at hY
      rw [hzt] at hY
      exact hY
    have hsh' : coverSheet z = k := by
      rw [← hget] at hsh
      rw [hzt] at hsh
      exact hsh
    exact ⟨hsh', hY'⟩
  let qUpper := q.induce (upperSheetVertices n k) hqSupport
  let stripWalk := qUpper.map (upperSheetOpenGraphHom n k hk A)
  let s := stripWalk.getVert 0
  let t := stripWalk.getVert stripWalk.length
  have hsY : s.1.2 = (coverBase (w.getVert (j+1))).2 := by
    simp [s, stripWalk, upperSheetOpenGraphHom, upperStripMap, qUpper, coverBase]
  have hsX : s.1.1 = (coverBase (w.getVert (j+1))).1 := by
    simp [s, stripWalk, upperSheetOpenGraphHom, upperStripMap, qUpper, coverBase]
  have htY : t.1.2 = (coverBase (w.getVert (i-1))).2 := by
    simp [t, stripWalk, upperSheetOpenGraphHom, upperStripMap, qUpper, hqEnd, coverBase]
  have htX : t.1.1 = (coverBase (w.getVert (i-1))).1 := by
    simp [t, stripWalk, upperSheetOpenGraphHom, upperStripMap, qUpper, hqEnd, coverBase]
  have hsEndpoint : s = (upperSheetOpenGraphHom n k hk A)
      ⟨w.getVert (j+1), hqSupport _ (by simp [q])⟩ := by
    change stripWalk.getVert 0 = _
    rw [SimpleGraph.Walk.getVert_zero]
  have hqEndMem : (w.drop (j+1)).getVert (i-j-2) ∈ q.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    refine ⟨q.length, ?_, le_rfl⟩
    rw [SimpleGraph.Walk.getVert_length]
  have htEndpoint : t = (upperSheetOpenGraphHom n k hk A)
      ⟨(w.drop (j+1)).getVert (i-j-2), hqSupport _ hqEndMem⟩ := by
    change stripWalk.getVert stripWalk.length = _
    rw [SimpleGraph.Walk.getVert_length]
  refine ⟨s,t,?_,?_,?_,?_,?_⟩
  · rw [hsY]
    exact hq0y
  · rw [htY]
    exact hq1y
  · rw [hsX]
    exact hq0x
  · rw [htX]
    exact hq1x
  · change (openGraph (ParafermionicStripGraph n)
      (embeddedConfigurationRestriction (ParafermionicStripGraph n)
        (ParafermionicAmbientGraph n) (parafermionicCoverStripEmbedding n k hk)
        (parafermionicCoverStrip_map_le n k hk) A)).Reachable s t
    rw [hsEndpoint, htEndpoint]
    exact stripWalk.reachable

end
end PottsContinuity.FKC.FiniteFK
