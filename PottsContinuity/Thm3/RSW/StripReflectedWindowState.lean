module

public import PottsContinuity.Thm3.RSW.StripReflectedWindowTop
public import PottsContinuity.Thm3.RSW.StripHorizontalReflection
public import PottsContinuity.Thm3.RSW.StripEventLimit

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The reflected sample reads the reflected original edge. -/
theorem stripHorizontalReflectionConfiguration_apply (n : ℕ) (c : ℤ)
    (ω : StripConfiguration n) (e : (stripGraph n).edgeSet) :
    stripHorizontalReflectionConfiguration n c ω e =
      ω ((stripHorizontalReflectionIso n c).mapEdgeSet e) := by
  have h := stripHorizontalReflectionConfiguration_edge n c ω
    ((stripHorizontalReflectionIso n c).mapEdgeSet e)
  have he := stripHorizontalReflection_edge_involutive n c e
  rwa [he] at h

/-- State reflection preserves the original coordinatewise open-edge order. -/
theorem stripHorizontalReflectionConfiguration_monotone (n : ℕ) (c : ℤ) :
    Monotone (stripHorizontalReflectionConfiguration n c) := by
  intro ω η h e
  simp only [stripHorizontalReflectionConfiguration_apply]
  exact h _

/-- Restricting a reflected inner window and closing its exterior is bounded
by reflecting the original larger window's actual sampled state. -/
theorem stripWindow_reflected_restriction_le (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N)
    (C : Configuration (PottsContinuity.squareLattice.induce
      (stripWindow n N : Set (ℤ × ℤ)))) :
    stripPlaneRestriction n (stripWindowPlaneConfiguration n M
      (embeddedConfigurationRestriction _ _
        (stripWindowReflectionEmbedding n M N c hMN)
        (stripWindowReflection_graph_le n M N c hMN) C)) ≤
      stripHorizontalReflectionConfiguration n c
        (stripPlaneRestriction n (stripWindowPlaneConfiguration n N C)) := by
  classical
  let f := stripWindowReflectionEmbedding n M N c hMN
  let hmap := stripWindowReflection_graph_le n M N c hMN
  intro e
  apply Bool.le_iff_imp.mpr
  intro h
  simp only [stripPlaneRestriction,stripWindowPlaneConfiguration,decide_eq_true_eq] at h
  obtain ⟨g,hg,hge⟩ := Finset.mem_map.mp h
  have hC := (mem_embeddedConfigurationRestriction _ _ f hmap C g).mp hg
  rw [stripHorizontalReflectionConfiguration_apply]
  simp only [stripPlaneRestriction,stripWindowPlaneConfiguration,decide_eq_true_eq]
  refine Finset.mem_map.mpr ⟨embeddedEdgeEmbedding _ _ f hmap g,hC,?_⟩
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map f g.val) =
    Sym2.map Subtype.val (Sym2.map (stripHorizontalReflectionIso n c) e.val)
  rw [Sym2.map_map,Sym2.map_map]
  change Sym2.map (fun z : (stripWindow n M : Set (ℤ × ℤ)) => (c-z.val.1,z.val.2)) g.val =
    Sym2.map (fun z : stripVertices n => (c-z.val.1,z.val.2)) e.val
  have hgeval : Sym2.map (fun z : (stripWindow n M : Set (ℤ × ℤ)) => z.val) g.val =
      Sym2.map (fun z : stripVertices n => z.val) e.val := by
    exact congrArg (fun e : PottsContinuity.squareLattice.edgeSet => e.val) hge
  have htrans := congrArg (Sym2.map (fun z : ℤ × ℤ => (c-z.1,z.2))) hgeval
  simp only [Sym2.map_map] at htrans
  change Sym2.map (fun z : (stripWindow n M : Set (ℤ × ℤ)) => (c-z.val.1,z.val.2)) g.val =
    Sym2.map (fun z : stripVertices n => (c-z.val.1,z.val.2)) e.val at htrans
  exact htrans

end
end PottsContinuity.RSW
