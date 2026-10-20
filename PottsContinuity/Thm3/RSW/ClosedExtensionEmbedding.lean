module

public import PottsContinuity.Thm3.RSW.FiniteDualClosure
public import PottsContinuity.Thm3.RSW.InducedConfiguration

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.RCInfinite
noncomputable section

/-- Including precisely the same original sampled lattice bonds into a larger
finite carrier does not change their whole-plane closed extension. -/
theorem finiteSubgraphConfiguration_embedded_closed_eq
    {S T : Finset LatticeVertex} (f : (S : Set LatticeVertex) ↪ (T : Set LatticeVertex))
    (hGH : (finiteLatticeGraph S).map f ≤ finiteLatticeGraph T)
    (hf : ∀ v, (f v).val = v.val) (A : Configuration (finiteLatticeGraph S)) :
    finiteSubgraphConfiguration T 0
      (embeddedConfigurationEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T) f hGH A) =
    finiteSubgraphConfiguration S 0 A := by
  classical
  have hmap : (embeddedConfigurationEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T) f hGH A).map
      (frozenEdgeEmbedding T) = A.map (frozenEdgeEmbedding S) := by
    rw [embeddedConfigurationEmbedding_eq_map,Finset.map_map]
    congr 1
    apply Function.Embedding.ext
    intro e
    apply Subtype.ext
    change Sym2.map Subtype.val (Sym2.map f e.val) = Sym2.map Subtype.val e.val
    rw [Sym2.map_map]
    congr 1
    exact funext hf
  funext e
  simp only [finiteSubgraphConfiguration,dite_true,hmap]

end
end PottsContinuity.RSW
