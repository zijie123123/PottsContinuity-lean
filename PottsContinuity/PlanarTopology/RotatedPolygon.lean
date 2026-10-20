module

public import PottsContinuity.FKC.Domains.PolygonDomain

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Reindex the same actual unit-edge polygon by a cyclic starting vertex. -/
def rotateLatticePolygon {m : ℕ} (P : FKC.LatticePolygon m) (a : ZMod (m+3)) :
    FKC.LatticePolygon m where
  vertex i := P.vertex (a+i)
  vertex_injective := fun _ _ h => add_left_cancel (P.vertex_injective h)
  adjacent i := by simpa only [add_assoc] using P.adjacent (a+i)

/-- Cyclic reindexing preserves the entire continuous boundary, not just vertices. -/
theorem rotateLatticePolygon_carrier {m : ℕ} (P : FKC.LatticePolygon m)
    (a : ZMod (m+3)) (δ : FKC.PositiveMesh) :
    (rotateLatticePolygon P a).carrier δ = P.carrier δ := by
  ext z
  simp only [FKC.LatticePolygon.carrier,Set.mem_iUnion]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨a+i,by simpa only [rotateLatticePolygon,add_assoc] using hi⟩
  · rintro ⟨i,hi⟩
    have h1 : a+(i-a) = i := by abel
    have h2 : a+(i-a+1) = i+1 := by abel
    exact ⟨i-a,by simpa only [rotateLatticePolygon,h1,h2] using hi⟩

/-- The bounded Jordan domain is independent of the cyclic starting label. -/
theorem rotateLatticePolygon_domain {m : ℕ} (P : FKC.LatticePolygon m)
    (a : ZMod (m+3)) (δ : FKC.PositiveMesh) :
    (rotateLatticePolygon P a).domain δ = P.domain δ := by
  simp only [FKC.LatticePolygon.domain,rotateLatticePolygon_carrier]

end PottsContinuity.PlanarTopology
