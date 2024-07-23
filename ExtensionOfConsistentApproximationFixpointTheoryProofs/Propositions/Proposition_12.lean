import ThesisProofs.Imports.Defs
import ThesisProofs.Imports.Ordered_Product
import ThesisProofs.Imports.Interlattice_Properties
import ThesisProofs.Imports.Bounded_Subtype
import ThesisProofs.Imports.Consistent_Approximating_Operator
import ThesisProofs.Imports.Reliable_Pair
import ThesisProofs.Imports.Stable_Revision_Operator
import ThesisProofs.Imports.Prudent_Pair
import ThesisProofs.Imports.Chain_Complete_Partial_Order

variable
  {D : Type u}
  {D1 D2 : D → Prop}
  [O : PartialOrder D]
  [BoundedPartialOrder D]
  [L1 : CompleteLatticeFromOrder (Subtype D1)]
  [L2 : CompleteLatticeFromOrder (Subtype D2)]
  (interlub : interlattice_lub D D1 D2)
  (interglb : interlattice_glb D D1 D2)
  (limitOrdinal : Ordinal)
  (isLimit : limitOrdinal.IsLimit)
  (chain : (@ChainCompletePartialOrder.Chain {x : Subtype D1 × Subtype D2 | ⊗x} (@InfoPoset _ _ _ O).toPreorder))

theorem OrdClassical (α β : Ordinal) : α ≤ β ∨ β < α := by
  apply Or.elim (Classical.em (α ≤ β))
  intro h; apply Or.inl h
  intro h; apply Or.inr; apply lt_of_not_le h


def Proposition_12_A :
L1.sSup {(chain i).val.1 | i < limitOrdinal} ≤ (L2.sInf {(chain i).val.2 | i < limitOrdinal}).val
:= by

  have p1 : ∀ u : Ordinal, ∀ κ : Ordinal, (chain κ).val.1 ≤ (chain u).val.2.val := by
    intro u κ
    apply (OrdClassical u κ).elim
    .
      intro h
      have h' : (u : Ordinal) ≤ (κ : Ordinal) := by
        aesop
      have t1 : (chain κ).val.1 ≤ (chain κ).val.2.val :=
        (chain κ).prop
      have t2 : (chain u) ≤ (chain κ) :=
        (@OrderHom.monotone _ _ _ (_) chain) h'
      have t3 : (chain κ).val.2.val ≤ (chain u).val.2 :=
        t2.2
      exact O.le_trans (chain κ).val.1 (chain κ).val.2.val (chain u).val.2 t1 t3
    .
      intro h
      have h' : (u : Ordinal) > (κ : Ordinal) := by
        aesop
      have t1 : (chain u).val.1 ≤ (chain u).val.2.val :=
        (chain u).prop
      have t2 : (chain κ) ≤ (chain u).val :=
         (@OrderHom.monotone _ _ _ (_) chain) (le_of_lt h')
      have t3 : (chain κ).val.1 ≤ (chain u).val.1 :=
        t2.1
      exact O.le_trans (chain κ).val.1 (chain u).val.1 (chain u).val.2.val t3 t1

  have p2 : ∀ u : Ordinal, (chain u).val.2.val ∈ upperBounds (Subtype.val '' {(chain i).val.1 | i < limitOrdinal}) := by
    intro u a ⟨a', ⟨i, ⟨_, ci_eq_a'⟩⟩, a_eq_a'⟩
    exact a_eq_a' ▸ ci_eq_a' ▸ p1 u i
  have p2' : ∀ u : Ordinal, ∀ x ∈ {(chain i).val.1 | i < limitOrdinal}, x ≤ (chain u).val.2.val := by
    intro u x x_in
    have b_ub : ∀ x ∈ (Subtype.val '' {(chain i).val.1 | i < limitOrdinal}), x ≤ (chain u).val.2.val :=  p2 u
    exact b_ub x (Set.mem_image_of_mem Subtype.val x_in)

  let aᵢₙ := L1.sSup {(chain i).val.1 | i < limitOrdinal}

  have p3 : ∀ u : Ordinal, aᵢₙ ≤ (chain u).val.2.val := by
    intro u
    exact interlub.2.2 (chain u).val.2 (chain u).val.2.prop {(chain i).val.1 | i < limitOrdinal} (p2' u)
  have p3' : ∀ b ∈ {(chain i).val.2 | i < limitOrdinal}, aᵢₙ ≤ b.val := by
    intro b ⟨i, ⟨_, ci_eq_b⟩⟩
    exact ci_eq_b ▸ p3 i

  have p4 : aᵢₙ.val ≤ L2.sInf {(chain i).val.2 | i < limitOrdinal} := by
    exact interglb.2.2 aᵢₙ.val aᵢₙ.prop {(chain i).val.2 | i < limitOrdinal} (p3')

  exact p4

-- Using the firstA assertion we can prove that this chain (with the supremum defined as in Proposition_12_A) can create an actual Omega Complete Partial Order, i.e. a chain with a supremum
def Proposition_12_B : ChainCompletePartialOrder {x : Subtype D1 × Subtype D2 | ⊗x} :=
{
  LimitOrdinal := limitOrdinal
  Is_Limit := isLimit
  cSup := λ c => ⟨(L1.sSup {(c i).val.1 | i < limitOrdinal}, L2.sInf {(c i).val.2 | i < limitOrdinal}), Proposition_12_A interlub interglb limitOrdinal c⟩
  le_cSup := λ c i => by
    apply And.intro
    .
      have a_in : (c i).val.1 ∈ {(c i).val.1 | i < limitOrdinal} := by
        aesop
      exact L1.le_sSup {(c i).val.1 | i < limitOrdinal} (c i).val.1 a_in
    .
      have b_in : (c i).val.2 ∈ {(c i).val.2 | i < limitOrdinal} := by
        aesop
      exact L2.sInf_le {(c i).val.2 | i < limitOrdinal} (c i).val.2 b_in

  cSup_le := λ c x h => by
    apply And.intro
    .
      have h1 : ∀ b ∈ {x | ∃ i < limitOrdinal, (c i).val.1 = x}, b ≤ x.val.1 := by
        exact λ b ⟨i, ⟨le_limit, ci_eq_b⟩⟩ => ci_eq_b ▸ (λ j => (h j).1) ⟨i, le_limit⟩

      exact L1.sSup_le {(c i).val.1 | i < limitOrdinal} x.val.1 h1
    .
      have h2 : ∀ b ∈ {x | ∃ i < limitOrdinal, (c i).val.2 = x}, x.val.2 ≤ b := by
        exact λ b ⟨i, ⟨le_limit, ci_eq_b⟩⟩ => ci_eq_b ▸ (λ j => (h j).2) ⟨i, le_limit⟩
      exact L2.le_sInf {(c i).val.2 | i < limitOrdinal} x.val.2 h2
}
