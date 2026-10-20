module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedExtremalSelector

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK Push BD12 Exploration
noncomputable section

/-- Source coordinates inspected by an auxiliary query. Fixed open edges
and edges outside the sampled mask carry no source variable. -/
def maskedSourceQuery {K V W : Type*} [Fintype K] [DecidableEq V] [DecidableEq W]
    (i : K ↪ V) (j : K ↪ W) (fixed queried : Finset W) : Finset V := by
  classical
  exact (Finset.univ.filter fun k => j k ∈ queried ∧ j k ∉ fixed).map i

/-- An auxiliary completion uses the embedded source variables and fixed
open bonds, with every other edge fixed closed. -/
def maskedCompletion {K V W : Type*} [Fintype K] [DecidableEq V] [DecidableEq W]
    (i : K ↪ V) (j : K ↪ W) (fixed : Finset W) (C : Finset V) : Finset W := by
  classical
  exact (Finset.univ.filter fun k => i k ∈ C).map j ∪ fixed

/-- Agreement on exactly the queried source variables fixes every queried
auxiliary state. This includes open and closed sampled states. -/
theorem maskedCompletion_agreement {K V W : Type*} [Fintype K] [DecidableEq V] [DecidableEq W]
    (i : K ↪ V) (j : K ↪ W) (fixed queried : Finset W) (C C' : Finset V)
    (h : C' ∩ maskedSourceQuery i j fixed queried = C ∩ maskedSourceQuery i j fixed queried) :
    maskedCompletion i j fixed C' ∩ queried = maskedCompletion i j fixed C ∩ queried := by
  classical
  have hstates (k : K) (hk : j k ∈ queried) (hfixed : j k ∉ fixed) : i k ∈ C' ↔ i k ∈ C := by
    have hquery : i k ∈ maskedSourceQuery i j fixed queried :=
      Finset.mem_map.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk,hfixed⟩,rfl⟩
    have he := Finset.ext_iff.mp h (i k)
    simpa only [Finset.mem_inter, hquery,and_true] using he
  ext e
  by_cases he : e ∈ queried
  · simp only [Finset.mem_inter,he,and_true]
    by_cases hf : e ∈ fixed
    · exact iff_of_true (Finset.mem_union_right _ hf) (Finset.mem_union_right _ hf)
    · simp only [maskedCompletion,Finset.mem_union,hf,or_false,Finset.mem_map,Finset.mem_filter,
        Finset.mem_univ,true_and]
      constructor <;> rintro ⟨k,hk,rfl⟩
      · exact ⟨k,(hstates k he hf).mp hk,rfl⟩
      · exact ⟨k,(hstates k he hf).mpr hk,rfl⟩
  · simp only [Finset.mem_inter,he,and_false]

local instance sourceQueryConfinedFintype (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) : Fintype (caseTwoConfinedPrefixGraph n s hfit b).edgeSet := Fintype.ofFinite _
local instance sourceQueryEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- The literal variable part of the padded raw left exploration, pulled
back to original source bonds. -/
def paddedPrefixSourceQueryReveal (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) :=
  maskedSourceQuery
    (embeddedEdgeEmbedding _ _ (Function.Embedding.refl _) (caseTwoConfinedPrefixGraph_map_le n s hfit b))
    (embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n) (confinedPrefix_padding_map_le n s hfit b))
    (prefixAuxRayBonds n s b)
    (intervalArmLeftReveal (2*n+1) (4*(s:ℤ)) (prefixAuxCompletion n s hfit b C))

/-- The padded completion agrees with the abstract finite-mask construction. -/
theorem prefixAuxCompletion_eq_maskedCompletion (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    prefixAuxCompletion n s hfit b C = maskedCompletion
      (embeddedEdgeEmbedding _ _ (Function.Embedding.refl _) (caseTwoConfinedPrefixGraph_map_le n s hfit b))
      (embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n) (confinedPrefix_padding_map_le n s hfit b))
      (prefixAuxRayBonds n s b) C := by
  classical
  ext e
  simp only [prefixAuxCompletion,maskedCompletion,embeddedConfigurationEmbedding_eq_map,
    Finset.mem_union,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
    caseTwoConfinedPrefixConfiguration,mem_embeddedConfigurationRestriction]

/-- The extremal trace is fixed by its actual queried source states. -/
theorem prefixAuxExtremalTrace_eq_of_source_query_agreement (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (b : CaseTwoTipEndpointRecord n s)
    (C C' : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (h : C' ∩ paddedPrefixSourceQueryReveal n s hfit b C =
      C ∩ paddedPrefixSourceQueryReveal n s hfit b C) :
    prefixAuxExtremalTrace n s hfit b C' = prefixAuxExtremalTrace n s hfit b C := by
  have hraw := maskedCompletion_agreement _ _ (prefixAuxRayBonds n s b)
    (intervalArmLeftReveal (2*n+1) (4*(s:ℤ)) (prefixAuxCompletion n s hfit b C)) C C' h
  rw [←prefixAuxCompletion_eq_maskedCompletion,←prefixAuxCompletion_eq_maskedCompletion] at hraw
  have hregion := intervalArmRightRegion_eq_of_raw_record_agreement (2*n+1) (4*(s:ℤ)) (5*(s:ℤ)) _ _ hraw
  unfold prefixAuxExtremalTrace intervalArmFilledLeftFrontier
  rw [hregion]

/-- Exact source locality follows from containment of the inspected source
variables in the literal stopped record `Push.caseTwoStoppedPrefixReveal`. This separate
helper retains its geometric premise explicitly. -/
theorem paddedExtremalConfinedPrefixSelector_isLocal_of_query_containment
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n)
    (hqueries : ∀ C b aux,
      caseTwoTipEndpointSelector n s hfit C=some b → 0<b.2.val.2 →
      prefixAuxExtremalTrace n s hfit b C=some aux →
      paddedPrefixSourceQueryReveal n s hfit b C ⊆
        caseTwoStoppedPrefixReveal n s hfit b (aux.map (prefixPaddingRetraction n))) :
    (paddedExtremalConfinedPrefixSelector n s hs hfit).IsLocal := by
  intro C C' b trace hb hy hsel hagree
  change (prefixAuxExtremalTrace n s hfit b C).map (List.map (prefixPaddingRetraction n))=some trace at hsel
  obtain ⟨aux,haux,rfl⟩ := Option.map_eq_some_iff.mp hsel
  have hsmall := recorded_agreement_of_subset C C' _ _ (hqueries C b aux hb hy haux) hagree
  change (prefixAuxExtremalTrace n s hfit b C').map (List.map (prefixPaddingRetraction n))=_
  rw [prefixAuxExtremalTrace_eq_of_source_query_agreement n s hfit b C C' hsmall,haux]
  rfl

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
