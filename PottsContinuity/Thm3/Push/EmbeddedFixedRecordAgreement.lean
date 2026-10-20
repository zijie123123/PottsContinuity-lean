module

public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Agreement on pulled-back original queries implies agreement on every
queried auxiliary state after the same fixed edges are added to both samples.
The statement includes closed states and all auxiliary edges outside the image. -/
theorem embedded_fixed_extension_record_agreement
    {V W : Type*} [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (K R : Configuration H) (C D : Configuration G)
    (hCD : D ∩ embeddedConfigurationRestriction G H f hGH R =
      C ∩ embeddedConfigurationRestriction G H f hGH R) :
    (embeddedConfigurationEmbedding G H f hGH D ∪ K) ∩ R =
      (embeddedConfigurationEmbedding G H f hGH C ∪ K) ∩ R := by
  classical
  have himage : ∀ e ∈ R,
      e ∈ embeddedConfigurationEmbedding G H f hGH D ↔
        e ∈ embeddedConfigurationEmbedding G H f hGH C := by
    intro e he
    rw [embeddedConfigurationEmbedding_eq_map,embeddedConfigurationEmbedding_eq_map]
    constructor
    · intro hd
      obtain ⟨d,hd,hde⟩ := Finset.mem_map.mp hd
      have hdR : d ∈ embeddedConfigurationRestriction G H f hGH R := by
        rw [mem_embeddedConfigurationRestriction,hde]
        exact he
      have hmem := Finset.ext_iff.mp hCD d
      have hdC := Finset.mem_inter.mp (hmem.mp (Finset.mem_inter.mpr ⟨hd,hdR⟩)) |>.1
      exact Finset.mem_map.mpr ⟨d,hdC,hde⟩
    · intro hc
      obtain ⟨d,hd,hde⟩ := Finset.mem_map.mp hc
      have hdR : d ∈ embeddedConfigurationRestriction G H f hGH R := by
        rw [mem_embeddedConfigurationRestriction,hde]
        exact he
      have hmem := Finset.ext_iff.mp hCD d
      have hdD := Finset.mem_inter.mp (hmem.mpr (Finset.mem_inter.mpr ⟨hd,hdR⟩)) |>.1
      exact Finset.mem_map.mpr ⟨d,hdD,hde⟩
  ext e
  by_cases he : e ∈ R
  · simp only [Finset.mem_inter,Finset.mem_union,he,and_true,himage e he]
  · simp only [Finset.mem_inter,he,and_false]

end
end PottsContinuity.Push
