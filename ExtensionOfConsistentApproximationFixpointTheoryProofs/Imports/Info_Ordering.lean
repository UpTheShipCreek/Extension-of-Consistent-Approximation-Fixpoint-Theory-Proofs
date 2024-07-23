import ThesisProofs.Imports.Defs
import ThesisProofs.Imports.Ordered_Product

instance {D : Type u} (D1 D2 : D → Prop) [PartialOrder D] : LT (Subtype D1 × Subtype D2) :=
{ lt := λ d d' => (d.1 < d'.1 ∧ d'.2 ≤ d.2) ∨ (d.1 ≤ d'.1 ∧ d'.2 < d.2) }

instance {D : Type u} (D1 D2 : D → Prop) [PartialOrder D] : LE (Subtype D1 × Subtype D2) :=
{ le := λ d d' => d.1 ≤ d'.1 ∧ d'.2 ≤ d.2 }
infixl:50 "≲" => (λ (a b : (Subtype _ × Subtype _)) => a ≤ b)

instance InfoPoset {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] : PartialOrder {x : Subtype D1 × Subtype D2 | ⊗x} :=
{
  le_refl := λ x => ⟨le_refl x.val.1, le_refl x.val.2⟩
  le_trans := λ _ _ _ h1 h2 => ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩
  le_antisymm := λ _ _ h1 h2 => Subtype.ext (Prod.ext (le_antisymm h1.1 h2.1) (le_antisymm h2.2 h1.2)),
  lt_iff_le_not_le := λ a b => by
    apply Iff.intro
    .
      intro h
      apply Or.elim h
      .
        intro h'
        apply And.intro
        .
          exact ⟨(le_not_le_of_lt h'.1).1, h'.2⟩
        .
          have t1 : ¬ b.val.1 ≤ a.val.1 := (le_not_le_of_lt h'.1).2
          have t2 : ¬ b.val.1 ≤ a.val.1 ∨ ¬ a.val.2 ≤ b.val.2 := Or.inl t1
          have t3 : ¬ (b.val.1 ≤ a.val.1 ∧ a.val.2 ≤ b.val.2) := by tauto
          tauto
      .
        intro h'
        apply And.intro
        .
          exact ⟨h'.1, (le_not_le_of_lt h'.2).1⟩
        .
          have t1 : ¬ a.val.2 ≤ b.val.2 := (le_not_le_of_lt h'.2).2
          have t2 : ¬ b.val.1 ≤ a.val.1 ∨ ¬ a.val.2 ≤ b.val.2 := Or.inr t1
          have t3 : ¬ (b.val.1 ≤ a.val.1 ∧ a.val.2 ≤ b.val.2) := by tauto
          tauto
    .
      intro h
      have t1 : a.val.1 ≤ b.val.1 ∧ b.val.2 ≤ a.val.2 := h.1
      apply Or.elim (Classical.em (a.val.1 < b.val.1))
      .
        intro h1
        apply Or.inl (And.intro h1 t1.2)
      .
        intro _
        have t2 : ¬ b.val.1 ≤ a.val.1 ∨ ¬ a.val.2 ≤ b.val.2 := by tauto
        apply t2.elim
        .
          intro h3
          exact Or.inl ⟨lt_of_le_not_le t1.1 h3, t1.2⟩
        .
          intro h3
          exact Or.inr ⟨t1.1, lt_of_le_not_le t1.2 h3⟩
}
