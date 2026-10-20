module

public import PottsContinuity.Thm3.OuterCircuit.InnerFaceContainment
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import PottsContinuity.Thm3.RSW.AnnulusRecordedSupport

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Exploration
open PottsContinuity.FKC

noncomputable section

local instance outerCircuitAnnulusSupportEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

local instance outerCircuitAnnulusSupportEdgeDecidableEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

local instance outerCircuitResidualSupportEdgeFintype {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Fintype (outerCircuitResidualGraph C).edgeSet := Fintype.ofFinite _

local instance outerCircuitResidualSupportEdgeDecidableEq {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    DecidableEq (outerCircuitResidualGraph C).edgeSet := Classical.decEq _

theorem outerCircuitPlusAnnulus_vertex_coordinate_bounds {n : ℕ}
    (v : OuterCircuitHostVertex n)
    (hv : v ∈ vertexBoxRegion (PottsContinuity.box (56*n))
      (5*(n:ℤ),0) (2*n)) :
    -(7*n:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ 7*n ∧
      -(7*n:ℤ) ≤ v.val.2 ∧ v.val.2 ≤ 7*n := by
  simp only [vertexBoxRegion, Set.mem_ofPred_eq] at hv
  rcases max_le_iff.mp hv with ⟨hx, hy⟩
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hy with ⟨hylo, hyhi⟩
  push_cast at *
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem outerCircuitMinusAnnulus_vertex_coordinate_bounds {n : ℕ}
    (v : OuterCircuitHostVertex n)
    (hv : v ∈ vertexBoxRegion (PottsContinuity.box (56*n))
      (-5*(n:ℤ),0) (2*n)) :
    -(7*n:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ 7*n ∧
      -(7*n:ℤ) ≤ v.val.2 ∧ v.val.2 ≤ 7*n := by
  simp only [vertexBoxRegion, Set.mem_ofPred_eq] at hv
  rcases max_le_iff.mp hv with ⟨hx, hy⟩
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hy with ⟨hylo, hyhi⟩
  push_cast at *
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem outerCircuitSelectedAnnulusEdge_in_recordedResidual {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hvalid : outerCircuitCandidateValid C p)
    (hn : 1 ≤ n)
    (z : PD.FK.LatticeVertex)
    (hz : z = (5*(n:ℤ),0) ∨ z = (-5*(n:ℤ),0))
    (e : (lemma4AmbientGraph n).edgeSet)
    (hregion : ∀ v ∈ e.val,
      v ∈ vertexBoxRegion (PottsContinuity.box (56*n)) z (2*n)) :
    e ∈ embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
      (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
      (outerCircuitResidualGraph_map_le C) Finset.univ := by
  rcases e with ⟨E, hE⟩
  induction E using Sym2.inductionOn with
  | _ x y =>
    have hxy : (lemma4AmbientGraph n).Adj x y := by simpa using hE
    have hxregion : x ∈ vertexBoxRegion
        (PottsContinuity.box (56*n)) z (2*n) := by
      apply hregion x
      simp [Sym2.mem_iff]
    have hyregion : y ∈ vertexBoxRegion
        (PottsContinuity.box (56*n)) z (2*n) := by
      apply hregion y
      simp [Sym2.mem_iff]
    have hxbounds : -(7*n:ℤ) ≤ x.val.1 ∧ x.val.1 ≤ 7*n ∧
        -(7*n:ℤ) ≤ x.val.2 ∧ x.val.2 ≤ 7*n := by
      rcases hz with rfl | rfl
      · exact outerCircuitPlusAnnulus_vertex_coordinate_bounds x hxregion
      · exact outerCircuitMinusAnnulus_vertex_coordinate_bounds x hxregion
    have hybounds : -(7*n:ℤ) ≤ y.val.1 ∧ y.val.1 ≤ 7*n ∧
        -(7*n:ℤ) ≤ y.val.2 ∧ y.val.2 ≤ 7*n := by
      rcases hz with rfl | rfl
      · exact outerCircuitPlusAnnulus_vertex_coordinate_bounds y hyregion
      · exact outerCircuitMinusAnnulus_vertex_coordinate_bounds y hyregion
    rcases hvalid with ⟨hcenter, hradial, hopen⟩
    have hdomain : outerCircuitClosedHalfCellBox (0,0) (7*n) ⊆
        (outerCircuitCodePolygon p).domain ⟨1, zero_lt_one⟩ := by
      apply outerCircuitPolygon_halfCellBox_subset_domain
        (outerCircuitCodePolygon p) (0,0) (7*n) hcenter
      intro i
      have hcast : ((7*n:ℕ):ℤ) = (7:ℤ) * (n:ℤ) := by norm_num [Nat.cast_mul]
      rw [hcast]
      simpa only [Prod.fst, Prod.snd, sub_zero] using (hradial i).1
    have hfacesBox := outerCircuitHostEdge_faceCenters_in_halfCellBox
      x y hxy hxbounds hybounds
    have hfaceTrue :
        (outerCircuitHostEdgeBond ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase true ∈
          (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩ :=
      (outerCircuitCodePolygon p).mem_interiorCellBases_iff ⟨1, zero_lt_one⟩ _ |>.2
        (hdomain (hfacesBox.1))
    have hfaceFalse :
        (outerCircuitHostEdgeBond ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩).faceBase false ∈
          (outerCircuitCodePolygon p).interiorCellBases ⟨1, zero_lt_one⟩ :=
      (outerCircuitCodePolygon p).mem_interiorCellBases_iff ⟨1, zero_lt_one⟩ _ |>.2
        (hdomain (hfacesBox.2))
    let e' : (lemma4AmbientGraph n).edgeSet :=
      ⟨s(x,y), (lemma4AmbientGraph n).mem_edgeSet.mpr hxy⟩
    have hnotReveal : e' ∉ outerCircuitSelectorReveal C := by
      rw [outerCircuitSelectorReveal_eq_candidateOutside C p hselected]
      intro hout
      have hnotBoth := (Finset.mem_filter.mp hout).2
      change ¬ ((∃ a ∈ outerCircuitCandidateInside p,
          a.val = (outerCircuitHostEdgeBond e').faceBase true) ∧
        (∃ b ∈ outerCircuitCandidateInside p,
          b.val = (outerCircuitHostEdgeBond e').faceBase false)) at hnotBoth
      let a : OuterCircuitHostVertex n :=
        ⟨(outerCircuitHostEdgeBond e').faceBase true,
          outerCircuitCandidateInteriorBase_mem_host C p hselected hn _ hfaceTrue⟩
      let b : OuterCircuitHostVertex n :=
        ⟨(outerCircuitHostEdgeBond e').faceBase false,
          outerCircuitCandidateInteriorBase_mem_host C p hselected hn _ hfaceFalse⟩
      have ha : a ∈ outerCircuitCandidateInside p := by
        simp only [outerCircuitCandidateInside, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hfaceTrue
      have hb : b ∈ outerCircuitCandidateInside p := by
        simp only [outerCircuitCandidateInside, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hfaceFalse
      exact hnotBoth ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    have hUnrevealed : (outerCircuitUnrevealedAmbientGraph C).Adj x y :=
      (outerCircuitUnrevealedAmbientGraph_adj C x y).2 ⟨hxy, by
        simpa only [e'] using hnotReveal⟩
    let u : OuterCircuitResidualVertices n C := ⟨x, Or.inl ⟨y, hUnrevealed⟩⟩
    let v : OuterCircuitResidualVertices n C := ⟨y, Or.inl ⟨x, hUnrevealed.symm⟩⟩
    have huv : (outerCircuitResidualGraph C).Adj u v := hUnrevealed
    let e₀ : (outerCircuitResidualGraph C).edgeSet :=
      ⟨s(u,v), (outerCircuitResidualGraph C).mem_edgeSet.mpr huv⟩
    rw [embeddedConfigurationEmbedding_eq_map]
    apply Finset.mem_map.mpr
    refine ⟨e₀, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    rw [embeddedEdgeEmbedding_coe]
    change Sym2.map Subtype.val (s(u,v)) = s(x,y)
    rw [Sym2.map_mk]

def outerCircuitResidualRecordedEdges {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Configuration (lemma4AmbientGraph n) :=
  embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
    (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
    (outerCircuitResidualGraph_map_le C) Finset.univ

def outerCircuitResidualAnnulusPairEvent {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Set (Configuration (outerCircuitResidualGraph C)) :=
  {A | embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
    (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
    (outerCircuitResidualGraph_map_le C) A ∈ lemma4AnnulusPairEvent n}

theorem outerCircuitEmbeddedRestriction_eq_inter_recordedEdges {n : ℕ}
    (C A : Configuration (lemma4AmbientGraph n)) :
    embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
      (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
      (outerCircuitResidualGraph_map_le C)
      (embeddedConfigurationRestriction (outerCircuitResidualGraph C)
        (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
        (outerCircuitResidualGraph_map_le C) A) =
      A ∩ outerCircuitResidualRecordedEdges C := by
  ext e
  rw [Finset.mem_inter]
  constructor
  · intro he
    rw [embeddedConfigurationEmbedding_eq_map] at he
    rcases Finset.mem_map.mp he with ⟨e₀, he₀, heq⟩
    subst e
    refine ⟨(mem_embeddedConfigurationRestriction _ _ _ _ A e₀).mp he₀, ?_⟩
    rw [outerCircuitResidualRecordedEdges, embeddedConfigurationEmbedding_eq_map]
    exact Finset.mem_map.mpr ⟨e₀, Finset.mem_univ _, rfl⟩
  · rintro ⟨heA, heR⟩
    rw [outerCircuitResidualRecordedEdges,
      embeddedConfigurationEmbedding_eq_map] at heR
    rcases Finset.mem_map.mp heR with ⟨e₀, _, heq⟩
    subst e
    rw [embeddedConfigurationEmbedding_eq_map]
    apply Finset.mem_map.mpr
    refine ⟨e₀, (mem_embeddedConfigurationRestriction _ _ _ _ A e₀).mpr ?_, rfl⟩
    exact heA

theorem outerCircuitResidualAnnulusPairEvent_isUpperSet {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    IsUpperSet (outerCircuitResidualAnnulusPairEvent C) := by
  intro A B hAB hA
  change embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
      (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
      (outerCircuitResidualGraph_map_le C) A ∈ lemma4AnnulusPairEvent n at hA
  have hmono : embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
      (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
      (outerCircuitResidualGraph_map_le C) A ⊆
    embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
      (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
      (outerCircuitResidualGraph_map_le C) B := by
    rw [embeddedConfigurationEmbedding_eq_map,
      embeddedConfigurationEmbedding_eq_map]
    exact Finset.map_subset_map.mpr hAB
  exact (lemma4AnnulusPairEvent_isUpperSet n) hmono hA

theorem outerCircuitSelectedResidualAnnulusPairEvent_iff {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (p : OuterCircuitPolygonCode n)
    (hselected : outerCircuitMaximumCandidate C = some (.inl p))
    (hvalid : outerCircuitCandidateValid C p)
    (hn : 1 ≤ n)
    (A : Configuration (lemma4AmbientGraph n)) :
    A ∈ lemma4AnnulusPairEvent n ↔
      embeddedConfigurationRestriction (outerCircuitResidualGraph C)
        (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
        (outerCircuitResidualGraph_map_le C) A ∈
          outerCircuitResidualAnnulusPairEvent C := by
  let R := outerCircuitResidualRecordedEdges C
  let Ares := embeddedConfigurationRestriction (outerCircuitResidualGraph C)
    (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
    (outerCircuitResidualGraph_map_le C) A
  let B := embeddedConfigurationEmbedding (outerCircuitResidualGraph C)
    (lemma4AmbientGraph n) (outerCircuitResidualEmbedding C)
    (outerCircuitResidualGraph_map_le C) Ares
  have hstate : A ∩ R = B ∩ R := by
    have hAstate : B = A ∩ R := by
      dsimp [B, Ares, R]
      exact outerCircuitEmbeddedRestriction_eq_inter_recordedEdges C A
    ext e
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨heA, heR⟩
      have heB : e ∈ B := by rw [hAstate]; exact Finset.mem_inter.mpr ⟨heA, heR⟩
      exact ⟨heB, heR⟩
    · rintro ⟨heB, heR⟩
      rw [hAstate] at heB
      simp only [Finset.mem_inter] at heB
      exact ⟨heB.1, heR⟩
  have hRplus : ∀ e : (lemma4AmbientGraph n).edgeSet,
      (∀ v ∈ e.val, v ∈ vertexBoxRegion (PottsContinuity.box (56*n))
        (5*(n:ℤ),0) (2*n)) → e ∈ R := by
    intro e he
    dsimp [R]
    exact outerCircuitSelectedAnnulusEdge_in_recordedResidual C p hselected hvalid hn
      (5*(n:ℤ),0) (Or.inl rfl) e he
  have hRminus : ∀ e : (lemma4AmbientGraph n).edgeSet,
      (∀ v ∈ e.val, v ∈ vertexBoxRegion (PottsContinuity.box (56*n))
        (-5*(n:ℤ),0) (2*n)) → e ∈ R := by
    intro e he
    dsimp [R]
    exact outerCircuitSelectedAnnulusEdge_in_recordedResidual C p hselected hvalid hn
      (-5*(n:ℤ),0) (Or.inr rfl) e he
  have hplus := annulus_event_visible_in_recorded_outerBonds
    (PottsContinuity.box (56*n)) (5*(n:ℤ),0) n R hRplus A B hstate
  have hminus := annulus_event_visible_in_recorded_outerBonds
    (PottsContinuity.box (56*n)) (-5*(n:ℤ),0) n R hRminus A B hstate
  change A ∈ finiteBoolEvent (PottsContinuity.box (56*n))
      (fun ω => ω ∈ annulusCircuitEvent (PottsContinuity.box (56*n))
        (5*(n:ℤ),0) n ∧
        ω ∈ annulusCircuitEvent (PottsContinuity.box (56*n))
          (-5*(n:ℤ),0) n) ↔
    B ∈ finiteBoolEvent (PottsContinuity.box (56*n))
      (fun ω => ω ∈ annulusCircuitEvent (PottsContinuity.box (56*n))
        (5*(n:ℤ),0) n ∧
        ω ∈ annulusCircuitEvent (PottsContinuity.box (56*n))
          (-5*(n:ℤ),0) n)
  simp only [finiteBoolEvent, Set.mem_ofPred_eq] at hplus hminus ⊢
  exact and_congr hplus hminus

end
end PottsContinuity.OuterCircuit
