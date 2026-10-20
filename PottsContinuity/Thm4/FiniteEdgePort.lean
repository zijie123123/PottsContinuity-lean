/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverFiniteEdgePort.lean`.
Adaptation: namespace relocation and PD edge embedding.
-/
module

public import PottsContinuity.Thm4.EdgePorts
public import PottsContinuity.Thm4.CoverToggle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open PottsContinuity.PD.FK PottsContinuity.Thm4 LatticeAxis LatticePort
noncomputable section

/-- Every actual edge of the whole cover is queried by a genuine lifted medial
port; the port retains the sheet of one of that edge's actual endpoints. -/
theorem parafermionicCoverPort_exists_for_edge
    (f : parafermionicCoverGraph.edgeSet) :
    ∃ c : ParafermionicCoverPort, parafermionicCoverPortEdge c = f := by
  classical
  obtain ⟨ab, hab⟩ := Sym2.mk_surjective f.1
  rcases ab with ⟨a, b⟩
  have hval : f.1 = s(a, b) := hab.symm
  have hadj : parafermionicCoverGraph.Adj a b := by
    apply parafermionicCoverGraph.mem_edgeSet.mp
    rw [← hval]
    exact f.2
  obtain ⟨bond, hb⟩ := LatticeBond.exists_of_adj hadj.1
  have hbases : s(bond.source, bond.target) = s(a.1, b.1) := by
    simpa [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target] using hb
  rcases Sym2.eq_iff.mp hbases with hdirect | hreverse
  · rcases hdirect with ⟨hsource, htarget⟩
    let c : ParafermionicCoverPort := (⟨bond, false, false⟩, a.2)
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [parafermionicCoverPortEdge_val, hval]
    change s((bond.source, a.2),
      (bond.target, a.2 + parafermionicCoverSheetShift bond.source bond.target)) = s(a, b)
    rw [hsource, htarget]
    exact Sym2.eq_iff.mpr (Or.inl
      ⟨Prod.ext rfl rfl, Prod.ext rfl hadj.2.symm⟩)
  · rcases hreverse with ⟨hsource, htarget⟩
    let c : ParafermionicCoverPort := (⟨bond, false, false⟩, b.2)
    have hrevSheet : a.2 = b.2 + parafermionicCoverSheetShift b.1 a.1 := by
      have hshift := parafermionicCoverSheetShift_reverse a.1 b.1
      rw [hshift, hadj.2]
      ring
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [parafermionicCoverPortEdge_val, hval]
    rw [show parafermionicCoverPortSourceSheet c = b.2 by
      simp [c, parafermionicCoverPortSourceSheet]]
    change s((bond.source, b.2),
      (bond.target, b.2 + parafermionicCoverSheetShift bond.source bond.target)) = s(a, b)
    rw [hsource, htarget]
    exact Sym2.eq_iff.mpr (Or.inr
      ⟨Prod.ext rfl rfl, Prod.ext rfl hrevSheet.symm⟩)

 /-- Both endpoints of every genuinely embedded finite-box edge are actual
vertices of the retained cover box. -/
theorem parafermionicCoverFiniteEdgeEmbedding_endpoints_mem (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ∀ v ∈ (parafermionicCoverFiniteEdgeEmbedding n e).1,
      v ∈ parafermionicCoverBoxVertices n := by
  have hbox : ∀ v ∈ (parafermionicCoverFiniteEdgeEmbedding n e).1,
      v ∈ parafermionicCoverBoxVertices n := by
    intro v hv
    obtain ⟨ab, hab⟩ := Sym2.mk_surjective e.1
    rcases ab with ⟨u, v'⟩
    have he : e.1 = s(u, v') := by simpa using hab.symm
    have heval : (parafermionicCoverFiniteEdgeEmbedding n e).1 =
        s(parafermionicCoverBoxVertexEmbedding n u,
          parafermionicCoverBoxVertexEmbedding n v') := by
      rw [parafermionicCoverFiniteEdgeEmbedding, embeddedEdgeEmbedding_coe]
      rw [he]
      simp [Function.Embedding.sym2Map_apply]
    have hv' : v = parafermionicCoverBoxVertexEmbedding n u ∨
        v = parafermionicCoverBoxVertexEmbedding n v' := by
      rw [heval] at hv
      exact (Sym2.mem_iff').mp hv
    rcases hv' with h | h
    · rw [h]
      exact u.2
    · rw [h]
      exact v'.2
  exact hbox

/-- Any embedded finite-box cover edge has a port in the retained finite carrier.
The support is the actual box-vertex condition, so both finite-edge endpoints
remain represented rather than dropping boundary half-ports. -/
theorem parafermionicCoverFinitePort_exists_for_edge (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ∃ c : PottsContinuity.Thm4.ParafermionicCoverFinitePort n,
      parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
  obtain ⟨c, hc⟩ := parafermionicCoverPort_exists_for_edge
    (parafermionicCoverFiniteEdgeEmbedding n e)
  refine ⟨⟨c, ?_⟩, ?_⟩
  · apply parafermionicCoverFiniteEdgeEmbedding_endpoints_mem n e
    rw [← hc]
    rw [parafermionicCoverPortEdge_eq_incident_pair]
    exact Sym2.mem_mk_left _ _
  · exact hc

end
end PottsContinuity.Thm4.Medial
