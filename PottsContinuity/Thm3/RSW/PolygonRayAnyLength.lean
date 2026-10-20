module

public import PottsContinuity.Thm3.RSW.PolygonRayTransport
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality

/-- Point location with an arbitrary polygon length index, matching existing
cycle-to-polygon consumers without casts or further geometric inputs. -/
theorem latticePolygon_mem_domain_of_nonzero_rayIndex
    {z : LatticeVertex} (p : PD.FK.squareLattice.Walk z z)
    {k : ℕ} (P : FKC.LatticePolygon k) (hlength : k+3 = p.length)
    (hp : p.IsCycle)
    (hvertices : ∀ i : ZMod (k+3), P.vertex i = p.getVert i.val)
    (x : LatticeVertex) (hindex : rayIndex x p ≠ 0)
    (hnot : ∀ i : ZMod (k+3), P.vertex i ≠ x) :
    FKC.latticeEmbed ⟨1,zero_lt_one⟩ x ∈ P.domain ⟨1,zero_lt_one⟩ := by
  have hmap := p.length_map polygonRayLatticeHom
  have hk : k = (p.map polygonRayLatticeHom).length-3 := by omega
  subst k
  exact latticePolygon_mem_domain_of_rayIndex_ne_zero p P hp hvertices x hindex hnot

end PottsContinuity.RSW
