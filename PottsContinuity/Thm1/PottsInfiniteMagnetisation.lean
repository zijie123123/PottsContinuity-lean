module

public import PottsContinuity.Thm1.CriticalPointTransfer
public import PottsContinuity.Thm1.PottsInfiniteLimit
public import PottsContinuity.Thm1.ShellMagnetisationLimit
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.FK.BoxExhaustion
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import PottsContinuity.WellDefined.Uniqueness

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

private lemma allClosed_adj_false (x y : LatticeVertex)
    (h : (rcInfiniteOpenGraph (fun _ : squareLattice.edgeSet => false)).Adj x y) : False := by
  rw [rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj] at h
  rcases h with ⟨hEdge, hne⟩
  rcases hEdge with ⟨hEdge, hOpen⟩
  simp at hOpen

private lemma reachable_allClosed_iff (x y : LatticeVertex) :
    (rcInfiniteOpenGraph (fun _ : squareLattice.edgeSet => false)).Reachable x y ↔ x = y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => rfl
    | cons hadj w ih => exact (allClosed_adj_false _ _ hadj).elim
  · intro hxy
    subst y
    exact SimpleGraph.Reachable.refl _

private lemma allClosed_origin_notInfinite :
    ¬ {y | (rcInfiniteOpenGraph (fun _ : squareLattice.edgeSet => false)).Reachable
        (0, 0) y}.Infinite := by
  have hCluster :
      {y | (rcInfiniteOpenGraph (fun _ : squareLattice.edgeSet => false)).Reachable
        (0, 0) y} = {(0, 0)} := by
    ext y
    simp [reachable_allClosed_iff]
  rw [hCluster]
  exact Set.Finite.not_infinite (Set.finite_singleton (0, 0))

theorem pottsInfiniteLimit_magnetisation_identity
    (q : ℕ) (hq : 2 ≤ q) (β : Set.Ici (0 : ℝ)) (i : Fin q)
    (μ : Measure (ℤ × ℤ → Fin q)) (hμ : IsPottsInfiniteVolumeLimit q β i μ)
    (ν : Measure (squareLattice.edgeSet → Bool))
    (hν : IsRCInfiniteVolumeLimit (pottsRCProbability β)
      ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ 1 ν) :
    μ.real {σ | σ (0, 0) = i} =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} := by
  let boxes : ℕ → Finset (ℤ × ℤ) := fun n => latticeBox (0, 0) n
  have hboxesMono : Monotone boxes := by
    intro m n hmn
    exact latticeBox_mono (0, 0) hmn
  have hboxesExhaust (x : ℤ × ℤ) : ∃ n, x ∈ boxes n :=
    origin_latticeBox_exhaustive x
  have hμseq : Tendsto
      (fun n => pottsEventProb (boxes n) (β : ℝ) i (fun σ => σ (0, 0) = i))
      atTop (𝓝 (μ.real {σ | σ (0, 0) = i})) := by
    simpa [boxes] using
      hμ.2 boxes hboxesMono hboxesExhaust ({(0, 0)} : Finset (ℤ × ℤ)) (fun _ => i)
  by_cases hβ0 : (β : ℝ) = 0
  · have hPottsConst : ∀ n,
        pottsEventProb (boxes n) 0 i (fun σ => σ (0, 0) = i) = 1 / (q : ℝ) := by
      intro n
      have hsub : ({(0, 0)} : Finset (ℤ × ℤ)) ⊆ boxes n := by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact center_mem_latticeBox (0, 0) n
      simpa [boxes, one_div] using
        pottsEventProb_zero_cylinder q i (boxes n) {(0, 0)} hsub (fun _ => i)
    have hconst : Tendsto
        (fun n => pottsEventProb (boxes n) 0 i (fun σ => σ (0, 0) = i))
        atTop (𝓝 (1 / (q : ℝ))) :=
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n =>
        (hPottsConst n).symm)
    have hμorigin : μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) :=
      tendsto_nhds_unique (by simpa [hβ0] using hμseq) hconst
    let qParam : Set.Ioi (0 : ℝ) :=
      ⟨(q : ℝ), by
        change (0 : ℝ) < (q : ℝ)
        exact_mod_cast (by omega : 0 < q)⟩
    have hpEndpoint : pottsRCProbability β = endpointParameter false := by
      apply Subtype.ext
      simp [pottsRCProbability, endpointParameter, hβ0]
    have hνEndpoint : IsRCInfiniteVolumeLimit (endpointParameter false) qParam 1 ν := by
      rw [← hpEndpoint]
      simpa [qParam] using hν
    have hDiracEndpoint := Foundations.endpoint_isRCInfiniteVolumeLimit_all_exhaustions
      qParam (1 : Fin 2) false
    have hνEq := WellDefined.limit_unique (endpointParameter false) qParam
      (1 : Fin 2) ν (Measure.dirac (fun _ : squareLattice.edgeSet => false))
      hνEndpoint hDiracEndpoint
    have hνorigin :
        ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0 := by
      rw [hνEq]
      simp [Measure.real_def, allClosed_origin_notInfinite]
    rw [hμorigin, hνorigin]
    ring
  · have hβpos : 0 < (β : ℝ) := lt_of_le_of_ne β.property (Ne.symm hβ0)
    let θ := pottsESParameters q (β : ℝ) (by omega) hβpos
    have hνθ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 ν := by
      have hp : θ.toP = pottsRCProbability β := by
        apply Subtype.ext
        rfl
      have hqθ : θ.toQ =
          ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ := by
        apply Subtype.ext
        rfl
      rw [hp, hqθ]
      exact hν
    have hνPD := Infinite.isRCInfiniteVolumeLimit_to_PD_box
      θ.toP θ.toQ 1 ν hνθ
    have hmag := pottsESOriginPinnedProbability_tendsto q hq (β : ℝ) hβpos i
      boxes (fun n => origin_latticeBox_nested n) hboxesExhaust ν (by simpa [θ] using hνPD)
    have hidentity := tendsto_nhds_unique hμseq hmag
    have hEvent :
        {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} =
          PottsContinuity.PD.RCInfinite.infiniteAt (0, 0) := by
      cases Foundations.squareLattice_eq_PD
      ext ω
      change {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite ↔
        ω ∈ PottsContinuity.PD.RCInfinite.infiniteAt (0, 0)
      rw [Foundations.rcInfiniteOpenGraph_eq_PD]
      rfl
    rw [hEvent]
    exact hidentity


theorem pottsInfiniteLimit_magnetisation_identity_all
    (q : ℕ) (hq : 1 ≤ q) (β : Set.Ici (0 : ℝ)) (i : Fin q)
    (μ : Measure (ℤ × ℤ → Fin q)) (hμ : IsPottsInfiniteVolumeLimit q β i μ)
    (ν : Measure (squareLattice.edgeSet → Bool))
    (hν : IsRCInfiniteVolumeLimit (pottsRCProbability β)
      ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ 1 ν) :
    μ.real {σ | σ (0, 0) = i} =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} := by
  by_cases hqone : q = 1
  · subst q
    have hleft : μ.real {σ | σ (0, 0) = i} = 1 := by
      let : IsProbabilityMeasure μ := hμ.1
      have hset : {σ : ℤ × ℤ → Fin 1 | σ (0, 0) = i} = Set.univ := by
        ext σ
        constructor
        · intro _
          trivial
        · intro _
          exact Subsingleton.elim (σ (0, 0)) i
      rw [hset]
      simp [Measure.real_def]
    rw [hleft]
    norm_num
  · exact pottsInfiniteLimit_magnetisation_identity q (by omega) β i μ hμ ν hν

end

end PottsContinuity.Thm1
