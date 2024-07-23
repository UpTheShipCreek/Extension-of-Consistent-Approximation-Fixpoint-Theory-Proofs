import Mathlib.Order.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.NaturalOps

-- Mirrored code from the Lean 4 repo
namespace ChainCompletePartialOrder

def Chain (α : Type u) [Preorder α] :=
  Ordinal →o α

namespace Chain

variable {α : Type u} {β : Type v} {γ : Type*}
variable [Preorder α] [Preorder β] [Preorder γ]

instance : FunLike (Chain α) Ordinal α := inferInstanceAs <| FunLike (Ordinal →o α) Ordinal α

instance : OrderHomClass (Chain α) Ordinal α := inferInstanceAs <| OrderHomClass (Ordinal →o α) Ordinal α

instance : CoeFun (Chain α) fun _ => Ordinal → α := ⟨DFunLike.coe⟩

instance [Inhabited α] : Inhabited (Chain α) :=
  ⟨⟨default, fun _ _ _ => le_rfl⟩⟩

instance : Membership α (Chain α) :=
  ⟨fun a (c : Ordinal →o α) => ∃ i, a = c i⟩


variable (c c' : Chain α)
variable (f : α →o β)
variable (g : β →o γ)

instance : LE (Chain α) where le x y := ∀ i, ∃ j, x i ≤ y j

lemma isChain_range : IsChain (· ≤ ·) (Set.range c) := Monotone.isChain_range (OrderHomClass.mono c)

lemma directed : Directed (· ≤ ·) c := directedOn_range.2 c.isChain_range.directedOn

/-- `map` function for `Chain` -/
-- Porting note: `simps` doesn't work with type synonyms
-- @[simps! (config := .asFn)]
def map : Chain β :=
  f.comp c

@[simp] theorem map_coe : ⇑(map c f) = f ∘ c := rfl

variable {f}

theorem mem_map (x : α) : x ∈ c → f x ∈ Chain.map c f :=
  fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩

theorem exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b :=
  fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩

@[simp]
theorem mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
  ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    subst b
    apply mem_map c _ h⟩

@[simp]
theorem map_id : c.map OrderHom.id = c :=
  OrderHom.comp_id _

theorem map_comp : (c.map f).map g = c.map (g.comp f) :=
  rfl

@[mono]
theorem map_le_map {g : α →o β} (h : f ≤ g) : c.map f ≤ c.map g :=
  fun i => by simp [mem_map_iff]; exists i; apply h

/-- `OmegaCompletePartialOrder.Chain.zip` pairs up the elements of two chains
that have the same index. -/
-- Porting note: `simps` doesn't work with type synonyms
-- @[simps!]
def zip (c₀ : Chain α) (c₁ : Chain β) : Chain (α × β) :=
  OrderHom.prod c₀ c₁

@[simp] theorem zip_coe (c₀ : Chain α) (c₁ : Chain β) (n : Ordinal) : c₀.zip c₁ n = (c₀ n, c₁ n) := rfl


end Chain

end ChainCompletePartialOrder

open ChainCompletePartialOrder

class ChainCompletePartialOrder (α : Type*) extends PartialOrder α where
  -- Limit Ordinal of the chain
  LimitOrdinal : Ordinal
  Is_Limit : LimitOrdinal.IsLimit
  -- The supremum of an increasing sequence
  cSup : Chain α → α
  -- `cSup` is an upper bound of the increasing sequence
  le_cSup : ∀ c : Chain α, ∀ (i : {x | x < LimitOrdinal}), c i ≤ cSup c
  -- `cSup` is a lower bound of the set of upper bounds of the increasing sequence
  cSup_le : ∀ (c : Chain α) (x), (∀ (i : {x | x < LimitOrdinal}), c i ≤ x) → cSup c ≤ x

namespace ChainCompletePartialOrder

variable {α : Type u} {β : Type v} {γ : Type*}
variable [ChainCompletePartialOrder α]

protected abbrev lift [PartialOrder β] (f : β →o α) (cSup₀ : Chain β → β)
    (h : ∀ x y, f x ≤ f y → x ≤ y) (h' : ∀ c, f (cSup₀ c) = cSup (c.map f)) :
    ChainCompletePartialOrder β :=
  sorry

theorem le_cSup_of_le {c : Chain α} {x : α} (i : Ordinal) (h : x ≤ c i) : x ≤ cSup c :=
  sorry

theorem cSup_total {c : Chain α} {x : α} (h : ∀ i, c i ≤ x ∨ x ≤ c i) : cSup c ≤ x ∨ x ≤ cSup c :=
  sorry

@[mono]
theorem cSup_le_cSup_of_le {c₀ c₁ : Chain α} (h : c₀ ≤ c₁) : cSup c₀ ≤ cSup c₁ :=
  sorry

theorem cSup_le_iff (c : Chain α) (x : α) : cSup c ≤ x ↔ ∀ i, c i ≤ x := by
  sorry
lemma isLUB_range_cSup (c : Chain α) : IsLUB (Set.range c) (cSup c) := by
  sorry

lemma cSup_eq_of_isLUB {c : Chain α} {a : α} (h : IsLUB (Set.range c) a) : a = cSup c := by
  sorry

/-- A subset `p : α → Prop` of the type closed under `cSup` induces an
`ChainCompletePartialOrder` on the subtype `{a : α // p a}`. -/
def subtype {α : Type*} [ChainCompletePartialOrder α] (p : α → Prop)
    (hp : ∀ c : Chain α, (∀ i ∈ c, p i) → p (cSup c)) : ChainCompletePartialOrder (Subtype p) :=
  ChainCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨cSup _, hp (c.map (OrderHom.Subtype.val p)) fun _ ⟨n, q⟩ => q.symm ▸ (c n).2⟩)
    (fun _ _ h => h) (fun _ => rfl)
