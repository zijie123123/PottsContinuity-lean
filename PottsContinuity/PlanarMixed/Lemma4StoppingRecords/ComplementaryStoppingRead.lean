module

public import PottsContinuity.Thm3.Push.CommonExplorationEvents

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK Exploration Push
noncomputable section
local instance complementarySourceEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- A literal complementary edge read. None denotes an unsampled original
bond, which is closed in the primal extension and hence open in the dual. -/
def complementaryEdgeRead {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (A : Configuration G) : Configuration H := by
  classical
  letI complementaryReadEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
  exact Finset.univ.filter (fun e => ∀ b, edge e=some b → b ∉ A)

@[simp] theorem mem_complementaryEdgeRead {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (A : Configuration G) (e : H.edgeSet) :
    e ∈ complementaryEdgeRead G H edge A ↔ ∀ b, edge e=some b → b ∉ A := by
  classical
  simp [complementaryEdgeRead]

/-- Pull an actual dual revealed edge set back to its sampled primal bonds.
Deterministic unsampled exterior bonds read no source variable. -/
def complementaryRevealPullback {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (S : Configuration H) : Configuration G := by
  classical
  exact S.biUnion (fun e => (edge e).toFinset)

theorem mem_complementaryRevealPullback {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (S : Configuration H) (b : G.edgeSet) :
    b ∈ complementaryRevealPullback G H edge S ↔ ∃ e ∈ S, edge e=some b := by
  classical
  simp [complementaryRevealPullback]

theorem complementaryEdgeRead_agreement {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (S : Configuration H) (A B : Configuration G)
    (h : B ∩ complementaryRevealPullback G H edge S = A ∩ complementaryRevealPullback G H edge S) :
    complementaryEdgeRead G H edge B ∩ S=complementaryEdgeRead G H edge A ∩ S := by
  classical
  ext e
  by_cases he : e ∈ S
  · have hread : (∀ b, edge e=some b → b ∉ B) ↔ (∀ b, edge e=some b → b ∉ A) := by
      constructor
      all_goals intro hb b heb
      all_goals
        have hm := (mem_complementaryRevealPullback G H edge S b).mpr ⟨e,he,heb⟩
        have heq := Finset.ext_iff.mp h b
        simp only [Finset.mem_inter,hm,and_true] at heq
      · exact fun ha => hb b heb (heq.mpr ha)
      · exact fun hb' => hb b heb (heq.mp hb')
    simpa only [Finset.mem_inter,he,and_true,mem_complementaryEdgeRead] using hread
  · simp only [Finset.mem_inter,he,and_false]

def complementaryStoppingReveal {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (reveal : RevealMap (G := H)) : RevealMap (G := G) :=
  fun A => complementaryRevealPullback G H edge (reveal (complementaryEdgeRead G H edge A))

theorem complementaryStoppingReveal_stable {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (reveal : RevealMap (G := H))
    (hstable : ∀ A B, B ∩ reveal A=A ∩ reveal A → reveal B=reveal A)
    (A B : Configuration G)
    (h : B ∩ complementaryStoppingReveal G H edge reveal A=A ∩ complementaryStoppingReveal G H edge reveal A) :
    complementaryStoppingReveal G H edge reveal B=complementaryStoppingReveal G H edge reveal A := by
  have heq := hstable _ _ (complementaryEdgeRead_agreement G H edge _ A B h)
  exact congrArg (complementaryRevealPullback G H edge) heq

theorem complementary_readFromReveal {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (edge : H.edgeSet → Option G.edgeSet)
    (reveal : RevealMap (G := H))
    (hstable : ∀ A B, B ∩ reveal A=A ∩ reveal A → reveal B=reveal A)
    (E : Set (Configuration H)) (hE : ReadFromReveal reveal E) :
    ReadFromReveal (complementaryStoppingReveal G H edge reveal)
      ((complementaryEdgeRead G H edge) ⁻¹' E) := by
  intro A B hB
  have hagree := complementaryEdgeRead_agreement G H edge _ A B hB.2
  exact hE _ _ ⟨hstable _ _ hagree,hagree⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
