-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RevealRecordDisintegration.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.MultiSeedClusterExploration

@[expose] public section

open scoped BigOperators
noncomputable section

namespace PottsContinuity.FKC.FiniteFK

variable {α β : Type*} [Fintype α] [Nonempty α]

local instance revealRangeFintype (r : α → β) : Fintype (Set.range r) := Fintype.ofFinite _

omit [Fintype α] [Nonempty α] in
 theorem filter_range_fiber_support (p : PMF α) (hp : ∀ a, p a ≠ 0)
    (r : α → β) (y : Set.range r) :
    ∃ a ∈ {a | r a = y.1}, a ∈ p.support := by
  obtain ⟨a, ha⟩ := y.2
  refine ⟨a, ha, ?_⟩
  exact (p.mem_support_iff a).2 (hp a)

omit [Nonempty α] in
/-- A full-support finite PMF decomposes over the literal attained range of any statistic.
The conditional PMF at a record is the normalized restriction to its exact fiber. -/
theorem pmf_eq_range_bind_filter (p : PMF α) (hp : ∀ a, p a ≠ 0) (r : α → β) :
    p = (p.map (Set.rangeFactorization r)).bind
      (fun y => p.filter {a | r a = y.1} (filter_range_fiber_support p hp r y)) := by
  classical
  ext x
  have hm (y : Set.range r) :
      (p.map (Set.rangeFactorization r)) y =
        ∑ a : α, if r a = y.1 then p a else 0 := by
    rw [PMF.map_apply, tsum_fintype]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : y = Set.rangeFactorization r a
    · have hr : r a = y.1 := by
        have hh := congrArg Subtype.val h.symm
        simpa using hh
      simp only [ite_eq_left h, ite_eq_left hr]
    · have hr : r a ≠ y.1 := by
        intro hr
        apply h
        exact Subtype.ext hr.symm
      simp only [ite_eq_right h, ite_eq_right hr]
  have hf (y : Set.range r) :
      (p.filter {a | r a = y.1} (filter_range_fiber_support p hp r y)) x =
        if r x = y.1 then p x * ((p.map (Set.rangeFactorization r)) y)⁻¹ else 0 := by
    rw [PMF.filter_apply]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [tsum_fintype]
    rw [← hm y]
    by_cases hxy : r x = y.1 <;> simp [hxy]
  rw [PMF.bind_apply]
  rw [tsum_fintype]
  simp_rw [hf]
  rw [Finset.sum_eq_single (Set.rangeFactorization r x)]
  · simp only [Set.rangeFactorization_coe]
    have hne : (p.map (Set.rangeFactorization r)) (Set.rangeFactorization r x) ≠ 0 := by
      apply (p.map (Set.rangeFactorization r)).mem_support_iff _ |>.1
      rw [PMF.support_map]
      exact Set.mem_image_of_mem _ ((p.mem_support_iff x).2 (hp x))
    have htop : (p.map (Set.rangeFactorization r)) (Set.rangeFactorization r x) ≠ ⊤ :=
      (p.map (Set.rangeFactorization r)).apply_ne_top _
    symm
    calc
      (p.map (Set.rangeFactorization r)) (Set.rangeFactorization r x) *
          (p x * ((p.map (Set.rangeFactorization r))
            (Set.rangeFactorization r x))⁻¹) =
        p x * ((p.map (Set.rangeFactorization r)) (Set.rangeFactorization r x) *
          ((p.map (Set.rangeFactorization r)) (Set.rangeFactorization r x))⁻¹) := by ac_rfl
      _ = p x := by rw [ENNReal.mul_inv_cancel hne htop, mul_one]
  · intro y hy hys
    have hxy : r x ≠ y.1 := by
      intro h
      apply hys
      exact Subtype.ext h.symm
    simp [hxy]
  · intro h
    exact (h (Finset.mem_univ _)).elim

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance revealRecordConfigurationFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance revealRecordConfigurationNonempty : Nonempty (Configuration G) := ⟨∅⟩
local instance revealRecordEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The literal attained record of an arbitrary configuration-dependent reveal:
the revealed edge set together with the actual open states on those edges. -/
def revealRecordStatistic (reveal : Configuration G → Configuration G) (C : Configuration G) :
    Configuration G × Configuration G :=
  (reveal C, C ∩ reveal C)

omit [Finite V] in
/-- The fiber of the literal pair-valued record is exactly the usual revealed-set
and revealed-state event, without any consistency hypothesis on `reveal`. -/
theorem revealRecordStatistic_fiber_eq (reveal : Configuration G → Configuration G)
    (C₀ : Configuration G) :
    {C | revealRecordStatistic reveal C = revealRecordStatistic reveal C₀} =
      revealRecordEvent G reveal C₀ := by
  ext C
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change reveal C = reveal C₀ at h₁
    change C ∩ reveal C = C₀ ∩ reveal C₀ at h₂
    refine ⟨h₁, ?_⟩
    calc
      C ∩ reveal C₀ = C ∩ reveal C := by rw [← h₁]
      _ = C₀ ∩ reveal C₀ := h₂
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext h₁
    change C ∩ reveal C = C₀ ∩ reveal C₀
    calc
      C ∩ reveal C = C ∩ reveal C₀ := by rw [h₁]
      _ = C₀ ∩ reveal C₀ := h₂

