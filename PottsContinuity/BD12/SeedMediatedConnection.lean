module

public import PottsContinuity.BD12.ClusterFrontier
public import PottsContinuity.BD12.StoppingDetermination

/-! The connection event witnessed through a seed vertex, and its exact
determination once all edges incident to the discovered seed clusters are known.
For a separating seed set it will equal the source connection event. -/

@[expose] public section

namespace PottsContinuity.BD12
open FKC.FiniteFK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance seedMediatedEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedMediatedEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Actual open connection from o to the target set, witnessed through some
seed s. This is defined on every configuration without a separation assumption. -/
def seedMediatedConnection (S B : Finset V) (o : V) (A : Configuration G) : Prop :=
  ∃ s, s ∈ S ∧ ∃ b, b ∈ B ∧ ActualConnected G A s o ∧ ActualConnected G A s b

/-- Indicator of the literal seed-mediated connection event. -/
def seedMediatedIndicator (S B : Finset V) (o : V) (A : Configuration G) : ℝ := by
  classical
  exact if seedMediatedConnection G S B o A then 1 else 0

/-- Once the frontier is exhausted, every completion has exactly the same
connectivity from each seed as the known open graph. Reuses the shared
q-independent single-cluster reveal-agreement theorem. -/
theorem seedClusterFrontier_empty_connected_iff (S : Finset V) (R H A : Configuration G)
    (hclosed : seedClusterFrontier G S R H = ∅) (hA : A ∩ R = H ∩ R)
    (s : V) (hs : s ∈ S) (u : V) :
    ActualConnected G A s u ↔ ActualConnected G (H ∩ R) s u := by
  classical
  have hM : actualMultiClusterReveal G S (H ∩ R) ⊆ R :=
    Finset.sdiff_eq_empty_iff_subset.mp hclosed
  have hsingle : actualClusterReveal G s (H ∩ R) ⊆ R :=
    (actualClusterReveal_subset_multi S (H ∩ R) hs).trans hM
  apply actualConnected_iff_of_reveal_agreement G s (H ∩ R) A
  calc
    A ∩ actualClusterReveal G s (H ∩ R) =
        (A ∩ R) ∩ actualClusterReveal G s (H ∩ R) := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsingle]
    _ = (H ∩ R) ∩ actualClusterReveal G s (H ∩ R) := by rw [hA]

/-- A completed frontier determines the seed-mediated observable on its whole
configuration fibre, including completions whose unknown edges are arbitrary. -/
theorem seedMediatedIndicator_determined_of_frontier_empty
    (S B : Finset V) (o : V) (R H : Configuration G)
    (hclosed : seedClusterFrontier G S R H = ∅) :
    finiteDetermines (seedMediatedIndicator G S B o) R H := by
  classical
  intro A hA
  have hconn (s : V) (hs : s ∈ S) (u : V) : ActualConnected G A s u ↔ ActualConnected G H s u :=
    (seedClusterFrontier_empty_connected_iff G S R H A hclosed hA s hs u).trans
      (seedClusterFrontier_empty_connected_iff G S R H H hclosed rfl s hs u).symm
  have hevent : seedMediatedConnection G S B o A ↔ seedMediatedConnection G S B o H := by
    constructor
    · rintro ⟨s, hs, b, hb, hso, hsb⟩
      exact ⟨s, hs, b, hb, (hconn s hs o).mp hso, (hconn s hs b).mp hsb⟩
    · rintro ⟨s, hs, b, hb, hso, hsb⟩
      exact ⟨s, hs, b, hb, (hconn s hs o).mpr hso, (hconn s hs b).mpr hsb⟩
  simp only [seedMediatedIndicator, hevent]

end
end PottsContinuity.BD12
