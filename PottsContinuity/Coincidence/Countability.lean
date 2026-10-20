module

public import PottsContinuity.Coincidence.ActivityMarginals
public import PottsContinuity.Coincidence.Set
public import PottsContinuity.WellDefined.Uniqueness
public import PottsContinuity.BD12.OrderedEdgeMarginalUniqueness
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Coincidence

open PottsContinuity
open PottsContinuity.BD12
open PottsContinuity.Critical
open PottsContinuity.PD.FK

noncomputable section

def positiveQ (q : Set.Ici (1 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(q : ℝ), Set.mem_Ioi.mpr
    (lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp q.2))⟩

private theorem positiveQ_ge_one (q : Set.Ici (1 : ℝ)) :
    1 ≤ (positiveQ q : ℝ) := by
  change 1 ≤ (q : ℝ)
  exact Set.mem_Ici.mp q.2

def closedProbability (p : Set.Ioo (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(p : ℝ), ⟨p.2.1.le, p.2.2.le⟩⟩

def probabilityToActivity (p : Set.Ioo (0 : ℝ) 1) : ℝ :=
  Real.log ((p : ℝ) / (1 - (p : ℝ)))

private theorem activityParameters_edgeParameter_of_probability
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (p : Set.Ioo (0 : ℝ) 1) :
    edgeParameter (activityParameters q hq (probabilityToActivity p)) = (p : ℝ) := by
  let r := (p : ℝ) / (1 - (p : ℝ))
  have hr : 0 < r := div_pos p.2.1 (sub_pos.mpr p.2.2)
  have hexp : Real.exp (probabilityToActivity p) = r := Real.exp_log hr
  have hβ : Real.exp (drtLogActivityTemperature (probabilityToActivity p) : ℝ) =
      1 + r := by
    rw [exp_drtLogActivityTemperature, hexp]
  have hneg : Real.exp (-(drtLogActivityTemperature (probabilityToActivity p) : ℝ)) =
      1 - (p : ℝ) := by
    rw [Real.exp_neg, hβ]
    dsimp [r]
    have hden : (1 : ℝ) - (p : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr p.2.2)
    field_simp [hden];
    ring
  rw [activityParameters, drtHomogeneousParameters_edgeParameter, hneg]
  ring

private theorem probabilityToActivity_injective :
    Function.Injective probabilityToActivity := by
  intro p p' h
  let q : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  have hq : 1 ≤ (q : ℝ) := by norm_num [q]
  have hmap := congrArg
    (fun s => edgeParameter (activityParameters q hq s)) h
  rw [activityParameters_edgeParameter_of_probability q hq p,
    activityParameters_edgeParameter_of_probability q hq p'] at hmap
  exact Subtype.ext hmap

private theorem free_wired_limits_equal_of_free_activity_continuity
    (q : Set.Ici (1 : ℝ)) (p : Set.Ioo (0 : ℝ) 1)
    (hcont : ContinuousAt (freeActivityEdgeMarginal (positiveQ q) (positiveQ_ge_one q))
      (probabilityToActivity p))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (closedProbability p) (positiveQ q) 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (closedProbability p) (positiveQ q) 1 μ₁) :
    μ₀ = μ₁ := by
  let q' := positiveQ q
  let s := probabilityToActivity p
  have hq := positiveQ_ge_one q
  let θ := activityParameters q' hq s
  let μc := freeActivityCanonicalLimit q' hq s
  let νc := wiredBoxCanonicalLimit θ
  have hθp : θ.toP = closedProbability p := by
    apply Subtype.ext
    change edgeParameter θ = (p : ℝ)
    exact activityParameters_edgeParameter_of_probability q' hq p
  have hθq : θ.toQ = q' := by
    apply Subtype.ext
    rfl
  have hμ₀θ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀ := by
    rw [hθp, hθq]
    exact hμ₀
  have hμ₁θ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ₁ := by
    rw [hθp, hθq]
    exact hμ₁
  have hμc := freeActivityCanonicalLimit_frozen q' hq s
  have hνc := wiredActivityCanonicalLimit_frozen q' hq s
  have hμ₀eq : μ₀ = μc.toMeasure :=
    PottsContinuity.WellDefined.limit_unique θ.toP θ.toQ 0 μ₀ μc.toMeasure
      hμ₀θ hμc
  have hμ₁eq : μ₁ = νc.toMeasure :=
    PottsContinuity.WellDefined.limit_unique θ.toP θ.toQ 1 μ₁ νc.toMeasure
      hμ₁θ hνc
  have hcommon₀ := frozen_limit_edge_probabilities_eq_horizontal θ.toP θ.toQ
    (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property 0 μ₀ hμ₀θ
  have hcommon₁ := frozen_limit_edge_probabilities_eq_horizontal θ.toP θ.toQ
    (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property 1 μ₁ hμ₁θ
  have hhorizontal :
      μ₀.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) =
        μ₁.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := by
    rw [hμ₀eq, hμ₁eq]
    change freeActivityEdgeMarginal q' hq s = wiredActivityEdgeMarginal q' hq s
    exact free_wired_activityEdgeMarginals_eq_of_free_continuous q' hq s hcont
  have hedge : ∀ e : squareLattice.edgeSet,
      μ₀.real {ω | ω e = true} = μ₁.real {ω | ω e = true} := by
    intro e
    rw [← allOpen_singleton_eq_edgeOpen e]
    calc
      μ₀.real (LatticeConfiguration.allOpen {e}) =
          μ₀.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := hcommon₀ e
      _ = μ₁.real (LatticeConfiguration.allOpen {horizontalUnitEdge}) := hhorizontal
      _ = μ₁.real (LatticeConfiguration.allOpen {e}) := (hcommon₁ e).symm
  exact free_eq_wired_of_edge_marginals θ μ₀ μ₁ hμ₀θ hμ₁θ hedge

theorem freeWiredDisagreementSet_countable (q : Set.Ici (1 : ℝ)) :
    (freeWiredDisagreementSet q).Countable := by
  let q' := positiveQ q
  have hq := positiveQ_ge_one q
  let bad : Set ℝ :=
    {s | ¬ ContinuousAt (freeActivityEdgeMarginal q' hq) s}
  have hbad : bad.Countable :=
    freeActivityEdgeMarginal_countableDiscontinuities q' hq
  let interiorDisagreements : Set (Set.Ioo (0 : ℝ) 1) :=
    {p | (p : ℝ) ∈ freeWiredDisagreementSet q}
  have hsubset : interiorDisagreements ⊆ probabilityToActivity ⁻¹' bad := by
    intro p hp
    obtain ⟨hp0, hp1, μ₀, μ₁, hμ₀, hμ₁, hne⟩ := hp
    have hμ₀' : IsRCInfiniteVolumeLimit (closedProbability p) (positiveQ q) 0 μ₀ := by
      simpa [closedProbability, positiveQ] using hμ₀
    have hμ₁' : IsRCInfiniteVolumeLimit (closedProbability p) (positiveQ q) 1 μ₁ := by
      simpa [closedProbability, positiveQ] using hμ₁
    by_contra hnot
    have hcont : ContinuousAt (freeActivityEdgeMarginal q' hq)
        (probabilityToActivity p) := by
      simpa [bad] using hnot
    have heq := free_wired_limits_equal_of_free_activity_continuity q p hcont
      μ₀ μ₁ hμ₀' hμ₁'
    exact hne heq
  have hpreimage : (probabilityToActivity ⁻¹' bad).Countable :=
    hbad.preimage probabilityToActivity_injective
  have hcount : interiorDisagreements.Countable := hpreimage.mono hsubset
  have himage : (Subtype.val '' interiorDisagreements).Countable :=
    hcount.image Subtype.val
  have heq : Subtype.val '' interiorDisagreements = freeWiredDisagreementSet q := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      obtain ⟨hp0, hp1, μ₀, μ₁, hμ₀, hμ₁, hne⟩ := hp
      have hpSet : p ∈ freeWiredDisagreementSet q :=
        ⟨hp0, hp1, μ₀, μ₁, hμ₀, hμ₁, hne⟩
      exact ⟨⟨p, ⟨hp0, hp1⟩⟩, hpSet, rfl⟩
  rw [← heq]
  exact himage

/-- Every nonempty interval contained in `(0,1)` contains a parameter where
the free and wired frozen limits coincide. -/
theorem exists_coincident_free_wired_limits_in_interval
    (q : Set.Ici (1 : ℝ)) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ p : Set.Ioo (0 : ℝ) 1,
      a < (p : ℝ) ∧ (p : ℝ) < b ∧
      ∃ μ₀ μ₁ : Measure LatticeConfiguration,
        IsRCInfiniteVolumeLimit
          ⟨(p : ℝ), ⟨p.2.1.le, p.2.2.le⟩⟩
          ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 0 μ₀ ∧
        IsRCInfiniteVolumeLimit
          ⟨(p : ℝ), ⟨p.2.1.le, p.2.2.le⟩⟩
          ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 1 μ₁ ∧
        μ₀ = μ₁ := by
  have hcount := freeWiredDisagreementSet_countable q
  have hdense : Dense (freeWiredDisagreementSet q)ᶜ :=
    Set.Countable.dense_compl ℝ hcount
  obtain ⟨p, hpnot, hpI⟩ := hdense.exists_mem_open
    (U := Set.Ioo a b) isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
  have hpab := Set.mem_Ioo.mp hpI
  have hp0 : 0 < p := lt_of_le_of_lt ha hpab.1
  have hp1 : p < 1 := lt_of_lt_of_le hpab.2 hb
  let pIoo : Set.Ioo (0 : ℝ) 1 := ⟨p, ⟨hp0, hp1⟩⟩
  let pIcc := closedProbability pIoo
  let q' := positiveQ q
  have hq := positiveQ_ge_one q
  obtain ⟨μ₀, hμ₀⟩ :=
    PottsContinuity.Foundations.exists_isRCInfiniteVolumeLimit
      pIcc q' hq 0
  obtain ⟨μ₁, hμ₁⟩ :=
    PottsContinuity.Foundations.exists_isRCInfiniteVolumeLimit
      pIcc q' hq 1
  have hpnot' : p ∉ freeWiredDisagreementSet q := by
    simpa only [Set.mem_compl_iff] using hpnot
  have hEq := free_wired_limits_equal_of_not_mem q p hp0 hp1 μ₀ μ₁ hμ₀ hμ₁ hpnot'
  refine ⟨pIoo, hpab.1, hpab.2, μ₀, μ₁, ?_, ?_, hEq⟩
  · change IsRCInfiniteVolumeLimit (closedProbability pIoo) (positiveQ q) 0 μ₀
    exact hμ₀
  · change IsRCInfiniteVolumeLimit (closedProbability pIoo) (positiveQ q) 1 μ₁
    exact hμ₁

end

end PottsContinuity.Coincidence
