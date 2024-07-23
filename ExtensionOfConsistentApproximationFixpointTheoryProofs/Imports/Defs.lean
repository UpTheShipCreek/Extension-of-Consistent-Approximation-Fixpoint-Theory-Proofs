import Init.Classical
import Mathlib.Order.CompleteLattice
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Basic
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.SetTheory.Ordinal.Arithmetic

import Mathlib.Tactic.Tauto

class BoundedPartialOrder (α : Type u) [PartialOrder α] extends BoundedOrder α

class CompleteLatticeFromOrder (α : Type u) [PartialOrder α] extends SupSet α, InfSet α, Sup α, Inf α, BoundedOrder α where
  le_refl : ∀ (a : α), a ≤ a
  le_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c
  lt_iff_le_not_le : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_antisymm : ∀ (a b : α), a ≤ b → b ≤ a → a = b
  le_sup_left : ∀ (a b : α), a ≤ a ⊔ b
  le_sup_right : ∀ (a b : α), b ≤ a ⊔ b
  sup_le : ∀ (a b c : α), a ≤ c → b ≤ c → a ⊔ b ≤ c
  inf_le_left : ∀ (a b : α), a ⊓ b ≤ a
  inf_le_right : ∀ (a b : α), a ⊓ b ≤ b
  le_inf : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c
  le_sSup : ∀ (s : Set α), ∀ a ∈ s, a ≤ sSup s
  sSup_le : ∀ (s : Set α) (a : α), (∀ b ∈ s, b ≤ a) → sSup s ≤ a
  sInf_le : ∀ (s : Set α), ∀ a ∈ s, sInf s ≤ a
  le_sInf : ∀ (s : Set α) (a : α), (∀ b ∈ s, a ≤ b) → a ≤ sInf s

instance CompleteLatticeFromOrder.toCL {α : Type u} [PartialOrder α] [L : CompleteLatticeFromOrder α] :
  CompleteLattice α where
      le_refl := L.le_refl
      le_top := L.le_top
      bot_le := L.bot_le
      le_trans := L.le_trans
      lt_iff_le_not_le := L.lt_iff_le_not_le
      le_antisymm := L.le_antisymm
      le_sup_left := L.le_sup_left
      le_sup_right := L.le_sup_right
      sup_le := L.sup_le
      inf_le_left := L.inf_le_left
      inf_le_right := L.inf_le_right
      le_inf := L.le_inf
      le_sSup := L.le_sSup
      sSup_le := L.sSup_le
      sInf_le := L.sInf_le
      le_sInf := L.le_sInf
