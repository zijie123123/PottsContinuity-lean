-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverSameSheetBridge.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRectangleBoundary
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalk
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

noncomputable section

local instance coverBridgeAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance coverBridgeAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

/-- The literal inclusion sends an open finite-cover walk into the full cover graph. -/
def parafermionicCoverBoxOpenWalkHom (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n)) :
    openGraph (ParafermionicAmbientGraph n) A →g parafermionicCoverGraph where
  toFun := fun v => v.1
  map_rel' := by
    intro u v huv
    have hbox : (ParafermionicAmbientGraph n).Adj u v := openGraph_le _ _ huv
    exact (parafermionicCoverBoxInclusionHom n).map_rel' hbox

/-- Any intermediate sheet is visited at an actual indexed vertex of an open walk. -/
theorem parafermionicCoverBoxOpenWalk_has_sheet_index
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (m : ℤ)
    (hm : (u.1.2 ≤ m ∧ m ≤ v.1.2) ∨ (v.1.2 ≤ m ∧ m ≤ u.1.2)) :
    ∃ i ≤ w.length, (w.getVert i).1.2 = m := by
  let f := parafermionicCoverBoxOpenWalkHom n A
  have hm' : ((f u).2 ≤ m ∧ m ≤ (f v).2) ∨ ((f v).2 ≤ m ∧ m ≤ (f u).2) := hm
  obtain ⟨z, hz, hzm⟩ := parafermionicCoverWalk_intermediate_sheet (w.map f) m hm'
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨a, ha, haz⟩ := hz
  have hval : (f a).2 = z.2 := congrArg Prod.snd haz
  obtain ⟨i, hi, hlen⟩ := (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp ha
  refine ⟨i, hlen, ?_⟩
  change (f (w.getVert i)).2 = m
  have hh : (w.map f).getVert i = z := by
    rw [SimpleGraph.Walk.getVert_map, hi, haz]
  have hmi : ((w.map f).getVert i).2 = m :=
    (congrArg Prod.snd hh).trans hzm
  simpa [SimpleGraph.Walk.getVert_map, parafermionicCoverBoxOpenWalkHom, f] using hmi

/-- A cover edge which raises the sheet coordinate is precisely a lower-seam edge
from base coordinate `(0,y)` to `(1,y)` with `y < 0`. -/
theorem parafermionicCover_adj_sheet_succ_coordinates
    {u v : ParafermionicCoverVertex} (h : parafermionicCoverGraph.Adj u v)
    (hs : v.2 = u.2 + 1) :
    u.1.1 = 0 ∧ v.1.1 = 1 ∧ u.1.2 = v.1.2 ∧ u.1.2 < 0 := by
  rw [parafermionicCoverGraph_adj_iff_cases] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all <;> omega

private theorem parafermionicCoverBoxOpenWalk_adj_sheet_bound
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (h : (openGraph (ParafermionicAmbientGraph n) A).Adj u v) :
    |v.1.2 - u.1.2| ≤ 1 := by
  have hc := (parafermionicCoverBoxOpenWalkHom n A).map_rel' h
  change |(parafermionicCoverBoxOpenWalkHom n A v).2 -
    (parafermionicCoverBoxOpenWalkHom n A u).2| ≤ 1
  exact parafermionicCover_adj_sheet_abs_le_one hc

private theorem parafermionicCoverBoxOpenWalk_firstIndex_ge_two
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (j : ℕ) (k : ℤ)
    (hstart : u.1.2 = k + 1)
    (hj : (w.getVert j).1.2 = k - 1) : 2 ≤ j := by
  by_contra hnot
  have hjlt : j < 2 := by omega
  interval_cases j
  · rw [SimpleGraph.Walk.getVert_zero] at hj
    omega
  · have hlen : 0 < w.length := by
      by_contra hle
      have hzero : w.length = 0 := by omega
      have huv : u = v := SimpleGraph.Walk.eq_of_length_eq_zero hzero
      subst v
      have heq := SimpleGraph.Walk.getVert_of_length_le w (i := 1) (by omega)
      rw [heq] at hj
      omega
    have hadj : (openGraph (ParafermionicAmbientGraph n) A).Adj
        (w.getVert 0) (w.getVert 1) :=
      SimpleGraph.Walk.adj_getVert_succ w hlen
    have hbound := parafermionicCoverBoxOpenWalk_adj_sheet_bound n A hadj
    have hdiff := abs_le.mp hbound
    rw [SimpleGraph.Walk.getVert_zero] at hdiff
    omega

private theorem walk_drop_take_getVert {V : Type*} {G : SimpleGraph V}
    {u v : V} (w : G.Walk u v) {a b t : ℕ}
    (_hab : a ≤ b) (_hb : b ≤ w.length) (ht : t ≤ b - a) :
    ((w.drop a).take (b - a)).getVert t = w.getVert (a + t) := by
  rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right ht,
    SimpleGraph.Walk.drop_getVert]

private theorem parafermionicCoverBoxOpenWalk_extract_indexed_core
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (k : ℤ) (hu : u.1.2 < k) (hv : k < v.1.2) :
    ∃ j i : ℕ,
      j ≤ w.length ∧
      (w.getVert j).1.2 = k + 1 ∧
      i ≤ j ∧
      2 ≤ i ∧
      (w.getVert (j - i)).1.2 = k - 1 ∧
      (∀ t, t < j → (w.getVert t).1.2 ≠ k + 1) ∧
      (∀ t, j - i < t → t ≤ j → (w.getVert t).1.2 ≠ k - 1) ∧
      (∀ t, 1 ≤ t → t < i → (w.getVert (j - i + t)).1.2 = k) := by
  classical
  let Pplus : ℕ → Prop := fun s => s ≤ w.length ∧ (w.getVert s).1.2 = k + 1
  have hplus : ∃ s, Pplus s := by
    obtain ⟨s, hs, hsheet⟩ := parafermionicCoverBoxOpenWalk_has_sheet_index
      n A w (k + 1) (by omega)
    exact ⟨s, hs, hsheet⟩
  let j := Nat.find hplus
  have hj : Pplus j := Nat.find_spec hplus
  have hjmin : ∀ s < j, ¬ Pplus s := fun s hs => Nat.find_min hplus hs
  have hnoPlus (s : ℕ) (hs : s < j) : (w.getVert s).1.2 ≠ k + 1 := by
    intro h
    exact hjmin s hs ⟨le_trans (Nat.le_of_lt hs) hj.1, h⟩
  let r := w.take j
  have hrlen : r.length = j := by
    dsimp [r]
    simp [Nat.min_eq_left hj.1]
  have hrplus : (r.getVert j).1.2 = k + 1 := by
    dsimp [r]
    rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_left (le_rfl : j ≤ j)]
    exact hj.2
  let rev := r.reverse
  have hrevlen : rev.length = j := by simp [rev, hrlen]
  have hrevzero : rev.getVert 0 = w.getVert j := by
    simp [rev, r,
      ]
  have hrevstart : (rev.getVert 0).1.2 = k + 1 := by
    rw [hrevzero]
    exact hj.2
  have hrevendEq : rev.getVert j = u := by
    calc
      rev.getVert j = rev.getVert rev.length := by rw [hrevlen]
      _ = u := SimpleGraph.Walk.getVert_length rev
  have hrevend : (rev.getVert j).1.2 = u.1.2 := congrArg (fun x : ParafermionicCoverBoxVertex n => x.1.2) hrevendEq
  let Pminus : ℕ → Prop := fun s => s ≤ rev.length ∧ (rev.getVert s).1.2 = k - 1
  have hminus : ∃ s, Pminus s := by
    have hbetween : u.1.2 ≤ k - 1 ∧ k - 1 ≤ (w.getVert j).1.2 := by
      constructor <;> omega
    obtain ⟨s, hs, hsheet⟩ := parafermionicCoverBoxOpenWalk_has_sheet_index
      n A rev (k - 1) (Or.inr hbetween)
    exact ⟨s, hs, hsheet⟩
  let i := Nat.find hminus
  have hi : Pminus i := Nat.find_spec hminus
  have himin : ∀ t < i, ¬ Pminus t := fun t ht => Nat.find_min hminus ht
  have hi2 : 2 ≤ i :=
    parafermionicCoverBoxOpenWalk_firstIndex_ge_two n A rev i k
      (by simpa [SimpleGraph.Walk.getVert_zero] using hrevstart) hi.2
  have hile : i ≤ j := by simpa [hrevlen] using hi.1
  have hrevNoMinus (t : ℕ) (ht : t < i) : (rev.getVert t).1.2 ≠ k - 1 := by
    intro h
    exact himin t ht ⟨le_trans (Nat.le_of_lt ht) hi.1, h⟩
  let s := rev.take i
  have hslen : s.length = i := by
    dsimp [s]
    simp [Nat.min_eq_left hi.1]
  let p := s.reverse
  have hindex (t : ℕ) (ht : t ≤ i) :
      p.getVert t = w.getVert (j - i + t) := by
    calc
      p.getVert t = s.getVert (s.length - t) := by
        simp [p, SimpleGraph.Walk.getVert_reverse]
      _ = s.getVert (i - t) := by rw [hslen]
      _ = rev.getVert (i - t) := by
        dsimp [s]
        rw [SimpleGraph.Walk.take_getVert,
          Nat.min_eq_right (Nat.sub_le i t)]
      _ = r.getVert (j - (i - t)) := by
        dsimp [rev]
        rw [SimpleGraph.Walk.getVert_reverse, hrlen]
      _ = w.getVert (j - i + t) := by
        dsimp [r]
        rw [SimpleGraph.Walk.take_getVert,
          Nat.min_eq_right (by omega : j - (i - t) ≤ j)]
        congr 1
        omega
  have hmiddle (t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t < i) :
      (w.getVert (j - i + t)).1.2 = k := by
    have hpos : j - i + t < j := by omega
    have hposle : j - i + t ≤ w.length := le_trans (Nat.le_of_lt hpos) hj.1
    have hnotlow : ¬ (w.getVert (j - i + t)).1.2 < k := by
      intro hlow
      let pos := j - i + t
      let tail := (w.drop pos).take (j - pos)
      have hposlen : pos ≤ w.length := by
        change j - i + t ≤ w.length
        exact hposle
      have hlenDrop : j - pos ≤ (w.drop pos).length := by
        rw [SimpleGraph.Walk.drop_length]
        exact Nat.sub_le_sub_right hj.1 pos
      have hlenTail : tail.length = j - pos := by
        dsimp [tail]
        rw [SimpleGraph.Walk.take_length, Nat.min_eq_left hlenDrop]
      have htake : tail.getVert (j - pos) = (w.drop pos).getVert (j - pos) := by
        dsimp [tail]
        rw [SimpleGraph.Walk.take_getVert,
          Nat.min_eq_left (le_rfl : j - pos ≤ j - pos)]
      have htail_end : (tail.getVert tail.length).1.2 = k + 1 := by
        rw [hlenTail]
        rw [htake, SimpleGraph.Walk.drop_getVert]
        have hsum : pos + (j - pos) = j := by
          change (j - i + t) + (j - (j - i + t)) = j
          omega
        rw [hsum]
        exact hj.2
      have htail_start : (tail.getVert 0).1.2 = (w.getVert pos).1.2 := by
        simp [tail, SimpleGraph.Walk.getVert_zero]
      have htail_end' : ((w.drop pos).getVert (j - pos)).1.2 = k + 1 := by
        have hidx : (tail.getVert tail.length) = (w.drop pos).getVert (j - pos) := by
          rw [hlenTail]
          exact htake
        rw [← hidx]
        exact htail_end
      have hlevel : (w.getVert pos).1.2 ≤ k - 1 ∧
          k - 1 ≤ ((w.drop pos).getVert (j - pos)).1.2 := by
        constructor
        · have hlow' : (w.getVert pos).1.2 < k := by simpa [pos] using hlow
          omega
        · rw [htail_end']
          omega
      obtain ⟨a, ha, hsheet⟩ := parafermionicCoverBoxOpenWalk_has_sheet_index
        n A tail (k - 1) (Or.inl hlevel)
      have hposA : a ≤ tail.length := ha
      have hback : (rev.getVert (j - (pos + a))).1.2 =
          (w.getVert (pos + a)).1.2 := by
        have hposa : pos + a ≤ j := by
          change j - i + t + a ≤ j
          omega
        dsimp [rev, r]
        rw [SimpleGraph.Walk.getVert_reverse, hrlen,
          SimpleGraph.Walk.take_getVert,
          Nat.min_eq_right (by omega : j - (j - (pos + a)) ≤ j)]
        have hcancel : j - (j - (pos + a)) = pos + a := by omega
        rw [hcancel]
      have htailval : (tail.getVert a).1.2 = (w.getVert (pos + a)).1.2 := by
        dsimp [tail]
        rw [SimpleGraph.Walk.take_getVert,
          Nat.min_eq_right (by omega : a ≤ j - pos),
          SimpleGraph.Walk.drop_getVert]
      have hrevbad : (rev.getVert (j - (pos + a))).1.2 = k - 1 := by
        rw [hback, ← htailval]
        exact hsheet
      have hindexlt : j - (pos + a) < i := by dsimp [pos]; omega
      exact hrevNoMinus _ hindexlt hrevbad
    have hnotupper : ¬ k < (w.getVert (j - i + t)).1.2 := by
      intro hupper
      let pre := w.take (j - i + t)
      have hprestart : (pre.getVert 0).1.2 = u.1.2 := by simp [pre]
      have hpreend : (pre.getVert pre.length).1.2 = (w.getVert (j - i + t)).1.2 := by
        simp [pre, SimpleGraph.Walk.take_length,
          Nat.min_eq_left hposle]
      have hlevel : u.1.2 ≤ k + 1 ∧
          k + 1 ≤ (w.getVert (j - i + t)).1.2 := by
        rw [← hprestart, ← hpreend]
        omega
      obtain ⟨a, ha, hsheet⟩ := parafermionicCoverBoxOpenWalk_has_sheet_index
        n A pre (k + 1) (Or.inl hlevel)
      have hale : a ≤ j - i + t := by
        have hlen : pre.length ≤ j - i + t := by
          simp [pre, SimpleGraph.Walk.take_length]
        exact le_trans ha hlen
      have hpreval : (pre.getVert a).1.2 = (w.getVert a).1.2 := by
        dsimp [pre]
        rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hale]
      have hbad : Pplus a := ⟨le_trans hale hposle, hpreval.symm.trans hsheet⟩
      exact hnoPlus a (by omega) hbad.2
    omega
  refine ⟨j, i, hj.1, hj.2, hile, hi2, ?_, ?_, ?_, ?_⟩
  · have hiw : (w.getVert (j - i)).1.2 = (rev.getVert i).1.2 := by
      dsimp [rev, r]
      rw [SimpleGraph.Walk.getVert_reverse, hrlen,
        SimpleGraph.Walk.take_getVert,
        Nat.min_eq_right (by omega : j - i ≤ j)]
    rw [hiw]
    exact hi.2
  · exact hnoPlus
  · intro t hlow hhigh hval
    have hrevEq : rev.getVert (j - t) = w.getVert t := by
      dsimp [rev, r]
      rw [SimpleGraph.Walk.getVert_reverse, hrlen,
        SimpleGraph.Walk.take_getVert,
        Nat.min_eq_right (by omega : j - (j - t) ≤ j)]
      have hcancel : j - (j - t) = t := by omega
      rw [hcancel]
    apply hrevNoMinus (j - t)
    · omega
    · rw [hrevEq]
      exact hval
  · intro t ht₁ ht₂
    exact hmiddle t ht₁ ht₂

/-- Any actual open-cover walk passing from below sheet `k` to above it contains
an actual open subwalk on sheet `k`, oriented from its lower seam to its upper seam. -/
theorem parafermionicCoverBoxOpenWalk_same_sheet_bridge
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    (k : ℤ) (hu : u.1.2 < k) (hv : k < v.1.2) :
    ∃ (a b : ParafermionicAmbientVertex n)
      (q : (openGraph (ParafermionicAmbientGraph n) A).Walk a b),
      (q.getVert 0).1.1.1 = 1 ∧ (q.getVert 0).1.1.2 < 0 ∧
      (q.getVert q.length).1.1.1 = 0 ∧ (q.getVert q.length).1.1.2 < 0 ∧
      (∀ z ∈ q.support, z.1.2 = k) := by
  classical
  obtain ⟨j, i, hjlen, hj, hile, hi2, hiLow, hnoPlus, hnoMinus, hmiddle⟩ :=
    parafermionicCoverBoxOpenWalk_extract_indexed_core n A w k hu hv
  have hi3 : 3 ≤ i := by
    by_contra hnot
    have hiEq : i = 2 := by omega
    subst i
    have hlow : (w.getVert (j - 2)).1.2 = k - 1 := by simpa using hiLow
    have hmid : (w.getVert (j - 1)).1.2 = k := by
      have := hmiddle 1 (by omega) (by omega)
      have heq : j - 2 + 1 = j - 1 := by omega
      rw [heq] at this
      exact this
    have hhigh : (w.getVert j).1.2 = k + 1 := by simpa using hj
    have hadj₁ : (openGraph (ParafermionicAmbientGraph n) A).Adj
        (w.getVert (j - 2)) (w.getVert (j - 1)) := by
      convert SimpleGraph.Walk.adj_getVert_succ w (i := j - 2) (by omega) using 1;
        congr 1; omega
    have hadj₂ : (openGraph (ParafermionicAmbientGraph n) A).Adj
        (w.getVert (j - 1)) (w.getVert j) := by
      convert SimpleGraph.Walk.adj_getVert_succ w (i := j - 1) (by omega) using 1;
        congr 1; omega
    have hcov₁ := (parafermionicCoverBoxOpenWalkHom n A).map_rel' hadj₁
    have hcov₂ := (parafermionicCoverBoxOpenWalkHom n A).map_rel' hadj₂
    have hraise₁ : (parafermionicCoverBoxOpenWalkHom n A (w.getVert (j - 1))).2 =
        (parafermionicCoverBoxOpenWalkHom n A (w.getVert (j - 2))).2 + 1 := by
      change (w.getVert (j - 1)).1.2 = (w.getVert (j - 2)).1.2 + 1
      omega
    have hraise₂ : (parafermionicCoverBoxOpenWalkHom n A (w.getVert j)).2 =
        (parafermionicCoverBoxOpenWalkHom n A (w.getVert (j - 1))).2 + 1 := by
      change (w.getVert j).1.2 = (w.getVert (j - 1)).1.2 + 1
      omega
    obtain ⟨_, htargetX, _, _⟩ := parafermionicCover_adj_sheet_succ_coordinates hcov₁ hraise₁
    obtain ⟨hsourceX, _, _, _⟩ := parafermionicCover_adj_sheet_succ_coordinates hcov₂ hraise₂
    have htarget : (w.getVert (j - 1)).1.1.1 = 1 := by
      change ((parafermionicCoverBoxOpenWalkHom n A).toFun (w.getVert (j - 1))).1.1 = 1 at htargetX
      exact htargetX
    have hsource : (w.getVert (j - 1)).1.1.1 = 0 := by
      change ((parafermionicCoverBoxOpenWalkHom n A).toFun (w.getVert (j - 1))).1.1 = 0 at hsourceX
      exact hsourceX
    omega
  let a := j - i + 1
  let b := j - 1
  have hab : a ≤ b := by dsimp [a, b]; omega
  have hb : b ≤ w.length := by dsimp [b]; omega
  let start : ParafermionicAmbientVertex n := w.getVert a
  let finish : ParafermionicAmbientVertex n :=
    (w.drop a).getVert (b - a)
  let q : (openGraph (ParafermionicAmbientGraph n) A).Walk start finish :=
    (w.drop a).take (b - a)
  have hlen : q.length = b - a := by
    dsimp [q]
    rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
      Nat.min_eq_left (Nat.sub_le_sub_right hb a)]
  have hqidx (t : ℕ) (ht : t ≤ b - a) :
      q.getVert t = w.getVert (a + t) := by
    dsimp [q]
    exact walk_drop_take_getVert w hab hb ht
  have hstart_idx : a = j - i + 1 := by rfl
  have hend_idx : b = j - 1 := by rfl
  have hstart_port : (w.getVert (j - i + 1)).1.1.1 = 1 ∧
      (w.getVert (j - i + 1)).1.1.2 < 0 := by
    have hadj : (openGraph (ParafermionicAmbientGraph n) A).Adj
        (w.getVert (j - i)) (w.getVert (j - i + 1)) := by
      exact SimpleGraph.Walk.adj_getVert_succ w (i := j - i) (by dsimp [a, b] at hab hb ⊢; omega)
    have hlowsheet : (w.getVert (j - i)).1.2 = k - 1 := hiLow
    have hnextsheet : (w.getVert (j - i + 1)).1.2 = k := by
      have := hmiddle 1 (by omega) (by omega)
      simpa using this
    have hraise : (parafermionicCoverBoxOpenWalkHom n A (w.getVert (j - i + 1))).2 =
        (parafermionicCoverBoxOpenWalkHom n A (w.getVert (j - i))).2 + 1 := by
      change (w.getVert (j - i + 1)).1.2 = (w.getVert (j - i)).1.2 + 1
      omega
    obtain ⟨_, hx, hy, hneg⟩ := parafermionicCover_adj_sheet_succ_coordinates
      ((parafermionicCoverBoxOpenWalkHom n A).map_rel' hadj) hraise
    constructor
    · have hx' : (w.getVert (j - i + 1)).1.1.1 = 1 := by
        change ((parafermionicCoverBoxOpenWalkHom n A).toFun (w.getVert (j - i + 1))).1.1 = 1 at hx
        exact hx
      exact hx'
    · have hy' : (parafermionicCoverBoxOpenWalkHom n A (w.getVert (j - i + 1))).1.2 < 0 := by
        change ((parafermionicCoverBoxOpenWalkHom n A).toFun (w.getVert (j - i + 1))).1.2 < 0
        rw [← hy]
        exact hneg
      change (w.getVert (j - i + 1)).1.1.2 < 0
      exact hy'
  have hend_port : (w.getVert (j - 1)).1.1.1 = 0 ∧
      (w.getVert (j - 1)).1.1.2 < 0 := by
    have hadj : (openGraph (ParafermionicAmbientGraph n) A).Adj
        (w.getVert (j - 1)) (w.getVert j) := by
      convert SimpleGraph.Walk.adj_getVert_succ w (i := j - 1) (by dsimp [b] at hb ⊢; omega) using 1;
        congr 1; omega
    have hprevsheet : (w.getVert (j - 1)).1.2 = k := by
      have := hmiddle (i - 1) (by omega) (by omega)
      have heq : j - i + (i - 1) = j - 1 := by omega
      rw [heq] at this
      exact this
    have hlastsheet : (w.getVert j).1.2 = k + 1 := by simpa using hj
    have hraise : (parafermionicCoverBoxOpenWalkHom n A (w.getVert j)).2 =
        (parafermionicCoverBoxOpenWalkHom n A (w.getVert (j - 1))).2 + 1 := by
      change (w.getVert j).1.2 = (w.getVert (j - 1)).1.2 + 1
      omega
    obtain ⟨hx, _, hy, hneg⟩ := parafermionicCover_adj_sheet_succ_coordinates
      ((parafermionicCoverBoxOpenWalkHom n A).map_rel' hadj) hraise
    constructor
    · change (w.getVert (j - 1)).1.1.1 = 0 at hx
      exact hx
    · change (w.getVert (j - 1)).1.1.2 < 0 at hneg
      exact hneg
  have hqstart : q.getVert 0 = w.getVert (j - i + 1) := by
    calc
      q.getVert 0 = w.getVert (a + 0) := hqidx 0 (by omega)
      _ = w.getVert (j - i + 1) := by congr 1
  have hqend : q.getVert q.length = w.getVert (j - 1) := by
    rw [hlen]
    have hidx := hqidx (b - a) (by omega)
    rw [hidx]
    have harith : a + (b - a) = j - 1 := by dsimp [a, b]; omega
    rw [harith]
  refine ⟨start, finish, q, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqstart]
    exact hstart_port.1
  · rw [hqstart]
    exact hstart_port.2
  · rw [hqend]
    exact hend_port.1
  · rw [hqend]
    exact hend_port.2
  ·
    intro z hz
    obtain ⟨t, hzt, ht⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    have ht' : t ≤ b - a := by simpa [hlen] using ht
    have hvertex := hqidx t ht'
    have hsheet := hmiddle (t + 1) (by omega) (by omega)
    have harith : a + t = j - i + (t + 1) := by dsimp [a]; omega
    rw [← hzt, hvertex, harith]
    exact hsheet


end
end PottsContinuity.FKC.FiniteFK
