-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/TerminalCounting.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.TerminalSeparation
public import PottsContinuity.PD.RCInfinite.TreeCounting

@[expose] public section

open Finset

namespace PottsContinuity.PD.RCInfinite
noncomputable section
open scoped Classical

def separatingTerminals {V : Type*} [Fintype V] (G : SimpleGraph V) (T : Set V) : Finset V :=
  Finset.univ.filter fun v => SeparatesThreeTerminals G T v

/-- In a finite connected graph, vertices separating three terminal
components are bounded by the terminal count. -/
theorem terminal_separator_card_add_two_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (T : Finset V) (hT : 2 ≤ T.card) :
    (separatingTerminals G (T : Set V)).card + 2 ≤ T.card := by
  obtain ⟨U, hTU, H, hHG, hH, hleaf⟩ := exists_terminal_tree G hG T
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < T.card)
  let : Nontrivial U := ⟨⟨⟨a, hTU ha⟩, ⟨b, hTU hb⟩,
    fun heq => hab (congrArg Subtype.val heq)⟩⟩
  let TU : Finset U := U.attach.filter fun v => v.val ∈ T
  have hTUmem (v : U) : v ∈ TU ↔ v.val ∈ T := by simp [TU]
  have hTUcard : TU.card = T.card := by
    apply Nat.le_antisymm
    · let f : TU → T := fun v => ⟨v.val.val, (hTUmem v).mp v.property⟩
      have hf : Function.Injective f := by
        intro v w h
        apply Subtype.ext
        exact Subtype.ext (congrArg (fun z : T => z.val) h)
      rw [← Fintype.card_coe TU, ← Fintype.card_coe T]
      exact Fintype.card_le_of_injective f hf
    · let f : T → TU := fun x => ⟨⟨x.val, hTU x.property⟩, by simp [TU, x.property]⟩
      have hf : Function.Injective f := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : TU => z.val.val) h
      rw [← Fintype.card_coe T, ← Fintype.card_coe TU]
      exact Fintype.card_le_of_injective f hf
  let B : Finset U := Finset.univ.filter fun v => 3 ≤ H.degree v
  have hEB : (separatingTerminals G (T : Set V)).card ≤ B.card := by
    let f : (separatingTerminals G (T : Set V)) → B := fun v =>
      let hv : SeparatesThreeTerminals G (T : Set V) v.val :=
        by simpa only [separatingTerminals, Finset.mem_filter, Finset.mem_univ, true_and]
          using v.property
      let hcarrier := separator_mem_connected_carrier (fun x hx => hTU hx)
        H hHG hH.connected hv
      ⟨⟨v.val, hcarrier⟩, by
        simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using
          separator_degree_ge_three (fun x hx => hTU hx) H hHG hH.connected hv hcarrier⟩
    have hf : Function.Injective f := by
      intro v w h
      apply Subtype.ext
      exact congrArg (fun z : B => z.val.val) h
    rw [← Fintype.card_coe (separatingTerminals G (T : Set V)), ← Fintype.card_coe B]
    exact Fintype.card_le_of_injective f hf
  have hbranch : B.card + 2 ≤ TU.card := by
    change (Finset.univ.filter fun v : U => 3 ≤ H.degree v).card + 2 ≤ TU.card
    exact tree_branch_card_le_terminals H hH TU (fun v hv =>
      (hTUmem v).mpr (hleaf v hv))
  omega

end
end PottsContinuity.PD.RCInfinite
