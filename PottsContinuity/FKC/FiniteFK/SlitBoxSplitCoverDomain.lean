-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitCoverDomain.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxInteriorCoverLift
public import PottsContinuity.FKC.FiniteFK.SlitBoxArcGeometry
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- A slit-box interior vertex has its canonical cover lift. -/
abbrev SlitBoxSplitInterior (n : ℕ) := SlitBoxInteriorVertex n

/-- Each wired-arc vertex is retained twice, once on each side of the cut. -/
abbrev SlitBoxArcSideVertex (n : ℕ) :=
  {v : SlitBoxVertex n // v ∈ slitBoxWiredArc n} × Bool

/-- Finite carrier for the cover cut along the wired arc: the interior has one
lift and every arc vertex has both side lifts. -/
abbrev SlitBoxSplitCoverVertex (n : ℕ) :=
  Sum (SlitBoxSplitInterior n) (SlitBoxArcSideVertex n)

/-- The explicit realization of the split carrier in the infinite cover graph. -/
def slitBoxSplitCoverMap (n : ℕ) : SlitBoxSplitCoverVertex n → ParafermionicCoverVertex
  | .inl v => slitBoxInteriorCoverLift n v
  | .inr ⟨v, side⟩ => (v.1.val, if side then 1 else 0)

theorem slitBoxSplitCoverMap_injective (n : ℕ) :
    Function.Injective (slitBoxSplitCoverMap n) := by
  intro a b hab
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      have huv := slitBoxInteriorCoverLift_injective n hab
      exact congrArg Sum.inl huv
    | inr v =>
      have hbase : u.1 ∈ slitBoxWiredArc n := by
        have hx := congrArg Prod.fst hab
        change u.1.val = v.1.1.val at hx
        have hsub : u.1 = v.1.1 := Subtype.ext hx
        rw [hsub]
        exact v.1.property
      exact (u.2 hbase).elim
  | inr u =>
    cases b with
    | inl v =>
      have hbase : v.1 ∈ slitBoxWiredArc n := by
        have hx := congrArg Prod.fst hab.symm
        change v.1.val = u.1.1.val at hx
        have hsub : v.1 = u.1.1 := Subtype.ext hx
        rw [hsub]
        exact u.1.property
      exact (v.2 hbase).elim
    | inr v =>
      have hbase : u.1.1.val = v.1.1.val := by
        have hx := congrArg Prod.fst hab
        change u.1.1.val = v.1.1.val at hx
        exact hx
      have hside : u.2 = v.2 := by
        have h := congrArg Prod.snd hab
        cases hu : u.2 <;> cases hv : v.2 <;>
          simp [slitBoxSplitCoverMap, hu, hv] at h ⊢
      have hslit : u.1.1 = v.1.1 := Subtype.ext hbase
      have harc : u.1 = v.1 := Subtype.ext hslit
      apply congrArg Sum.inr
      apply Prod.ext
      · exact harc
      · exact hside

def slitBoxSplitCoverBoundary (n : ℕ) : Set (SlitBoxSplitCoverVertex n) :=
  Set.range (fun v : SlitBoxArcSideVertex n => Sum.inr v)

theorem slitBoxSplitCoverBoundary_nonempty (n : ℕ) :
    (slitBoxSplitCoverBoundary n).Nonempty := by
  obtain ⟨v, hv⟩ := slitBoxWiredArc_nonempty n
  refine ⟨Sum.inr (⟨v, hv⟩, false), ?_⟩
  exact ⟨(⟨v, hv⟩, false), rfl⟩

theorem slitBoxSplitCoverMap_inl_not_boundary (n : ℕ)
    (v : SlitBoxSplitInterior n) :
    Sum.inl v ∉ slitBoxSplitCoverBoundary n := by
  rintro ⟨w, hw⟩
  rcases w with ⟨a, side⟩
  cases hw

/-- Pull back cover adjacency and cut every edge whose endpoints are both
boundary side-lifts. All carrier vertices are retained. -/
def slitBoxSplitCoverGraph (n : ℕ) : SimpleGraph (SlitBoxSplitCoverVertex n) where
  Adj u v := parafermionicCoverGraph.Adj (slitBoxSplitCoverMap n u)
      (slitBoxSplitCoverMap n v) ∧
    ¬ (u ∈ slitBoxSplitCoverBoundary n ∧ v ∈ slitBoxSplitCoverBoundary n)
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, fun hboth => h.2 ⟨hboth.2, hboth.1⟩⟩
  loopless := by
    constructor
    intro u h
    exact parafermionicCoverGraph.loopless.irrefl _ h.1

@[simp] theorem slitBoxSplitCoverGraph_adj_iff (n : ℕ)
    (u v : SlitBoxSplitCoverVertex n) :
    (slitBoxSplitCoverGraph n).Adj u v ↔
      parafermionicCoverGraph.Adj (slitBoxSplitCoverMap n u)
        (slitBoxSplitCoverMap n v) ∧
        ¬ (u ∈ slitBoxSplitCoverBoundary n ∧ v ∈ slitBoxSplitCoverBoundary n) := Iff.rfl

theorem slitBoxSplitCoverGraph_interior_adj_iff (n : ℕ)
    (u v : SlitBoxSplitInterior n) :
    (slitBoxSplitCoverGraph n).Adj (Sum.inl u) (Sum.inl v) ↔
      (slitBoxGraph n).Adj u.1 v.1 := by
  change (parafermionicCoverGraph.Adj (slitBoxInteriorCoverLift n u)
      (slitBoxInteriorCoverLift n v) ∧
      ¬ (Sum.inl u ∈ slitBoxSplitCoverBoundary n ∧
        Sum.inl v ∈ slitBoxSplitCoverBoundary n)) ↔
    (slitBoxGraph n).Adj u.1 v.1
  simp [slitBoxSplitCoverBoundary, slitBoxInteriorCoverLift_adj_iff]

theorem slitBoxSplitCoverGraph_boundary_neighbor_unique (n : ℕ)
    (u : SlitBoxSplitInterior n) (v w : SlitBoxSplitCoverVertex n)
    (hv : v ∈ slitBoxSplitCoverBoundary n)
    (hw : w ∈ slitBoxSplitCoverBoundary n)
    (huv : (slitBoxSplitCoverGraph n).Adj (Sum.inl u) v)
    (huw : (slitBoxSplitCoverGraph n).Adj (Sum.inl u) w) : v = w := by
  rcases hv with ⟨⟨vBase, vSide⟩, rfl⟩
  rcases hw with ⟨⟨wBase, wSide⟩, rfl⟩
  have huOutside : u.1 ∉ slitBoxWiredArc n := u.2
  have hbaseV : (slitBoxGraph n).Adj u.1 vBase.1 := by
    apply (slitBoxGraph_adj_iff n u.1 vBase.1).2
    refine ⟨huv.1.1, ?_⟩
    intro hboth
    exact huOutside ((mem_slitBoxWiredArc_iff n u.1).mpr hboth.1)
  have hbaseW : (slitBoxGraph n).Adj u.1 wBase.1 := by
    apply (slitBoxGraph_adj_iff n u.1 wBase.1).2
    refine ⟨huw.1.1, ?_⟩
    intro hboth
    exact huOutside ((mem_slitBoxWiredArc_iff n u.1).mpr hboth.1)
  have hsame : vBase.1 = wBase.1 :=
    slitBoxGraph_adj_wiredArc_unique n huOutside vBase.2 wBase.2 hbaseV hbaseW
  have hvCover : parafermionicCoverGraph.Adj
      (slitBoxInteriorCoverLift n u) (slitBoxSplitCoverMap n (Sum.inr (vBase, vSide))) := huv.1
  have hwCover : parafermionicCoverGraph.Adj
      (slitBoxInteriorCoverLift n u) (slitBoxSplitCoverMap n (Sum.inr (wBase, wSide))) := huw.1
  have hvUnique := parafermionicCoverNeighborLift_unique (slitBoxInteriorCoverLift n u)
    vBase.1.val (slitBoxSplitCoverMap n (Sum.inr (vBase, vSide))) rfl hvCover
  have hwUnique := parafermionicCoverNeighborLift_unique (slitBoxInteriorCoverLift n u)
    wBase.1.val (slitBoxSplitCoverMap n (Sum.inr (wBase, wSide))) rfl hwCover
  have hval : (slitBoxSplitCoverMap n (Sum.inr (vBase, vSide))) =
      (slitBoxSplitCoverMap n (Sum.inr (wBase, wSide))) := by
    rw [hvUnique, hwUnique]
    congr 1
    exact congrArg Subtype.val hsame
  apply congrArg Sum.inr
  apply Prod.ext
  · apply Subtype.ext
    exact hsame
  · have := congrArg Prod.snd hval
    have hside : vSide = wSide := by
      cases vSide <;> cases wSide <;>
        simp [slitBoxSplitCoverMap] at this ⊢
    exact hside

end PottsContinuity.FKC.FiniteFK
