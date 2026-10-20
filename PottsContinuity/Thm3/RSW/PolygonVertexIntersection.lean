module

public import PottsContinuity.Thm3.RSW.PolygonIntersection

/-! # Intersecting unit lattice polygons have a shared original vertex -/

@[expose] public section

namespace PottsContinuity.RSW
open Set

/-- Euclidean intersection of two unit lattice polygon boundaries produces
an actual common lattice vertex, also when the two chosen edges coincide. -/
theorem latticePolygon_shared_vertex_of_carriers_inter
    {m k : ℕ} (P : FKC.LatticePolygon m) (Q : FKC.LatticePolygon k)
    (δ : FKC.PositiveMesh) (hinter : (P.carrier δ ∩ Q.carrier δ).Nonempty) :
    ∃ i : ZMod (m+3), ∃ j : ZMod (k+3), P.vertex i = Q.vertex j := by
  classical
  obtain ⟨z,hzP,hzQ⟩ := hinter
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hzP
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hzQ
  by_cases hedge : s(P.vertex i,P.vertex (i+1)) = s(Q.vertex j,Q.vertex (j+1))
  · rcases Sym2.eq_iff.mp hedge with ⟨h₁,_⟩ | ⟨h₁,_⟩
    · exact ⟨i,j,h₁⟩
    · exact ⟨i,j+1,h₁⟩
  · have hend := FKC.mem_inter_lattice_segments_endpoints δ
      (P.adjacent i) (Q.adjacent j) hedge ⟨hi,hj⟩
    rcases hend.1 with hP | hP <;> rcases hend.2 with hQ | hQ
    · exact ⟨i,j,(FKC.latticeEmbed_injective δ) (hP.symm.trans hQ)⟩
    · exact ⟨i,j+1,(FKC.latticeEmbed_injective δ) (hP.symm.trans hQ)⟩
    · exact ⟨i+1,j,(FKC.latticeEmbed_injective δ) (hP.symm.trans hQ)⟩
    · exact ⟨i+1,j+1,(FKC.latticeEmbed_injective δ) (hP.symm.trans hQ)⟩

/-- For the annulus chain it suffices to establish overlapping Jordan
interiors and the two genuine nonnesting witnesses. -/
theorem latticePolygon_shared_vertex_of_overlapNonnesting
    {m k : ℕ} (P : FKC.LatticePolygon m) (Q : FKC.LatticePolygon k)
    (δ : FKC.PositiveMesh) (hoverlap : (P.domain δ ∩ Q.domain δ).Nonempty)
    (houtP : ∃ z ∈ P.carrier δ, z ∉ closure (Q.domain δ))
    (houtQ : ∃ z ∈ Q.carrier δ, z ∉ closure (P.domain δ)) :
    ∃ i : ZMod (m+3), ∃ j : ZMod (k+3), P.vertex i = Q.vertex j :=
  latticePolygon_shared_vertex_of_carriers_inter P Q δ
    (latticePolygon_carriers_inter_of_overlapNonnesting P Q δ hoverlap houtP houtQ)

end PottsContinuity.RSW
