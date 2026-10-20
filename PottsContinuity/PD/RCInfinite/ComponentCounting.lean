-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/ComponentCounting.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

open Finset

namespace PottsContinuity.PD.RCInfinite
noncomputable section
open scoped Classical

def componentPart {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (c : G.ConnectedComponent) : Finset V :=
  S.filter fun v => G.connectedComponentMk v = c

def componentPartSubtype {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (c : G.ConnectedComponent) : Finset c :=
  Finset.univ.filter fun v => v.val ∈ S

theorem componentPartSubtype_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (c : G.ConnectedComponent) :
    (componentPartSubtype G S c).card = (componentPart G S c).card := by
  classical
  let A := componentPartSubtype G S c
  let B := componentPart G S c
  apply Nat.le_antisymm
  · let f : A → B := fun x => ⟨x.val.val, by
      have hx : x.val.val ∈ S := by simpa [A, componentPartSubtype] using x.property
      change x.val.val ∈ componentPart G S c
      simpa only [componentPart, Finset.mem_filter, Finset.mem_univ, true_and] using
        (show x.val.val ∈ S ∧ G.connectedComponentMk x.val.val = c from
          ⟨hx, x.val.property⟩)⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact Subtype.ext (congrArg (fun z : B => z.val) h)
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe] using hc
  · let f : B → A := fun x => ⟨⟨x.val, (by
        have hx : x.val ∈ S ∧ G.connectedComponentMk x.val = c := by
          simpa [B, componentPart] using x.property
        exact hx.2)⟩,
      by
        have hx : x.val ∈ S ∧ G.connectedComponentMk x.val = c := by
          simpa [B, componentPart] using x.property
        change ⟨x.val, hx.2⟩ ∈ componentPartSubtype G S c
        simpa only [componentPartSubtype, Finset.mem_filter, Finset.mem_univ, true_and] using
          hx.1⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : A => z.val.val) h
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe] using hc

theorem sum_componentPart_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] (S : Finset V) :
    ∑ c : G.ConnectedComponent, (componentPart G S c).card = S.card := by
  classical
  calc
    ∑ c : G.ConnectedComponent, (componentPart G S c).card =
        ∑ c : G.ConnectedComponent, ∑ v ∈ S,
          if G.connectedComponentMk v = c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [componentPart, Finset.sum_boole, Nat.cast_id]
    _ = ∑ v ∈ S, ∑ c : G.ConnectedComponent,
          if G.connectedComponentMk v = c then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = S.card := by simp

end
end PottsContinuity.PD.RCInfinite
