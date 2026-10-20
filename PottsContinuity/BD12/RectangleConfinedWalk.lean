module

public import PottsContinuity.BD12.RectangleOpenGraphs
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Horizontal crossings as actual whole-plane open walks confined to the
literal rectangle. This interface keeps all original open bonds. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section

/-- Exact whole-plane walk characterization of the finite induced crossing. -/
theorem horizontalRectangle_iff_confined_open_walk (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) :
    ω ∈ horizontalRectangle a w h ↔
      ∃ (u v : LatticeVertex) (p : (PD.rcInfiniteOpenGraph ω).Walk u v),
        u.1 = a.1 ∧ v.1 = a.1+(w : ℤ) ∧
          ∀ z ∈ p.support, z ∈ latticeRectangle a w h := by
  have hg := embeddedRestriction_domainGraph (latticeRectangle a w h) ω
  constructor
  · rintro ⟨u,v,hu,hv,hconn⟩
    have hconn' : ((PD.rcInfiniteOpenGraph ω).induce (latticeRectangle a w h : Set LatticeVertex)).Reachable u v :=
      Eq.mp (congrArg (fun G : SimpleGraph (RectangleVertex a w h) => G.Reachable u v) hg) hconn
    obtain ⟨p⟩ := hconn'
    let f : (PD.rcInfiniteOpenGraph ω).induce (latticeRectangle a w h : Set LatticeVertex) →g
        PD.rcInfiniteOpenGraph ω := { toFun := Subtype.val, map_rel' := fun h => h }
    refine ⟨u.val,v.val,p.map f,(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    exact x.property
  · rintro ⟨u,v,p,hu,hv,hall⟩
    have hum := hall u p.start_mem_support
    have hvm := hall v p.end_mem_support
    let u' : RectangleVertex a w h := ⟨u,hum⟩
    let v' : RectangleVertex a w h := ⟨v,hvm⟩
    have hconn : ((PD.rcInfiniteOpenGraph ω).induce (latticeRectangle a w h : Set LatticeVertex)).Reachable u' v' :=
      ⟨p.induce _ hall⟩
    refine ⟨u',v',Finset.mem_filter.mpr ⟨hum,hu⟩,Finset.mem_filter.mpr ⟨hvm,hv⟩,?_⟩
    exact Eq.mpr (congrArg (fun G : SimpleGraph (RectangleVertex a w h) => G.Reachable u' v') hg) hconn

end
end PottsContinuity.BD12
