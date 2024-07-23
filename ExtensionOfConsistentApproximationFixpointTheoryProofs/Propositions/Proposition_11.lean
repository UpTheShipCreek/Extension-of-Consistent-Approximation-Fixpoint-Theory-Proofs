import ThesisProofs.Imports.Defs
import ThesisProofs.Imports.Ordered_Product
import ThesisProofs.Imports.Interlattice_Properties
import ThesisProofs.Imports.Bounded_Subtype
import ThesisProofs.Imports.Consistent_Approximating_Operator
import ThesisProofs.Imports.Reliable_Pair
import ThesisProofs.Imports.Stable_Revision_Operator
import ThesisProofs.Imports.Prudent_Pair

import ThesisProofs.Propositions.Proposition_10

variable
{D : Type u}
{D1 D2 : D → Prop}
[O : PartialOrder D]
[BoundedPartialOrder D]
[L1 : CompleteLatticeFromOrder (Subtype D1)]
[L2 : CompleteLatticeFromOrder (Subtype D2)]
(interlub : interlattice_lub D D1 D2)
(interglb : interlattice_glb D D1 D2)
(A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
(conA : consistent_approximating_operator A)
(ab : {x // prudent interlub A conA x})

def Proposition_11_A :
-- (a, b) ≲ (b↓, a↑)
(ab.1.1.1.1, ab.1.1.1.2) ≲ ((rOb interlub A conA ab).val,(rOa interglb A conA ab).val) ∧
-- reliable A (b↓, a↑)
reliable A ⟨((rOb interlub A conA ab).val, (rOa interglb A conA ab).val), (Proposition_10 interlub interglb A conA ab).2.2.2⟩ := by

  let a := ab.1.1.1.1
  let b := ab.1.1.1.2

  let A₁ := A₁OrderHom interlub A conA ab
  let A₂ := A₂OrderHom interglb A conA ab

  let bᵥ := (rOb interlub A conA ab)
  let aᵤ := (rOa interglb A conA ab)

  let P10 := Proposition_10 interlub interglb A conA ab

  -- (a, b) ≲ (b↓, a↑)
  have p1 : (a, b) ≲ (bᵥ.val, aᵤ.val) :=
    ⟨ab.prop, P10.2.2.1⟩

  -- (b↓, b) ≲ (b↓, a↑)
  have p2 : (bᵥ.val, b) ≲ (bᵥ, aᵤ) := by
    apply And.intro
    .
      rfl
    .
      exact P10.2.2.1

  -- A (b↓, b) ≲ A (b↓, a↑)
  have p3 : A ⟨(bᵥ.val, b), P10.1⟩  ≲ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val :=
    conA ⟨(bᵥ.val, b), P10.1⟩ ⟨(bᵥ, aᵤ),P10.2.2.2⟩ p2

  -- A(b↓, b)₁ = b↓
  have p4 : (A ⟨(bᵥ.val, b), P10.1⟩).val.1 = bᵥ := by
    have b_d_fix: A₁ bᵥ = bᵥ := @OrderHom.map_lfp {x // (boundedSubtype _ _ _ D1 ⊥ b) x} (Proposition_8_A b interlub) A₁
    have notation_eq : A₁ bᵥ = (A ⟨(bᵥ.val, b), P10.1⟩).val.1 := by
      tauto
    rw [←notation_eq]
    rw [b_d_fix]

  -- b↓ ≤ A(b↓, a↑)₁
  have p5 : bᵥ ≤ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val.1 := by
    have proof := p3.1
    rw [p4] at proof
    exact proof

  -- (a, a↑) ≲ (b↓, a↑)
  have p6 : (a, aᵤ) ≲ (bᵥ, aᵤ) := by
    apply And.intro
    .
      exact ab.prop
    .
      rfl

  -- A(a, a↑) ≲ A(b↓, a↑)
  have p7 : A ⟨(a, aᵤ), P10.2.1⟩ ≲ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val :=
    conA ⟨(a, aᵤ), P10.2.1⟩ ⟨(bᵥ, aᵤ.val), P10.2.2.2⟩ p6

  -- A(a, a↑)₂ = a↑
  have p8 : A₂ aᵤ = aᵤ :=
    @OrderHom.map_lfp {x // (boundedSubtype _ _ _ D2 a ⊤) x} (Proposition_8_B a interglb) A₂
  have p8' : A₂ aᵤ = (A ⟨(a, aᵤ), P10.2.1⟩).val.2 := by
    tauto

  -- A (b↓, a↑)₂ ≤ a↑
  have p9 : (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩).val.2 ≤ aᵤ := by
    have proof := p7.2
    rw [←p8', p8] at proof
    exact proof

  -- (b↓, a↑) ≲ A (b↓, a↑)
  have p10 : (bᵥ.val, aᵤ.val) ≲ (A ⟨(bᵥ, aᵤ), P10.2.2.2⟩) := by
    exact ⟨p5, p9⟩

  exact ⟨p1, p10⟩

-- In Proposition 11 need to take the lfp of A(·, a↑)₁
-- For that we need to prove that A(·, a↑)₁ : L → L is a monotone operator
-- Where X is a Complete Lattice
  -- So we take X = [⊥, a↑]₁, we need to prove that [⊥, a↑]₁ is a complete lattice
  -- And that ⊥ ≤ A(·, a↑)₁ ≤ a↑, i.e. that A(·, a↑)₁ ∈ [⊥, a↑]₁

def Proposition_11_B : prudent interlub A conA ⟨⟨(rOb interlub A conA ab, (rOa interglb A conA ab)), (Proposition_10 interlub interglb A conA ab).2.2.2⟩, (Proposition_11_A interlub interglb A conA ab).2⟩ :=

  let b := ab.1.1.1.2

  let P10 := Proposition_10 interlub interglb A conA ab
  let P11A := Proposition_11_A interlub interglb A conA ab

  let aᵤ := (rOa interglb A conA ab)
  let bᵥ := (rOb interlub A conA ab)

  let CLaᵤ := Proposition_8_A aᵤ.val interlub
  let CLb  := Proposition_8_A b interlub

  let A₁ := A₁OrderHom interlub A conA ab
  let Aₛ := A₁OrderHom interlub A conA ⟨⟨(bᵥ, aᵤ), P10.2.2.2⟩, P11A.2⟩

  -- let aₛ := L1.sSup {x | x.val ≤ aᵤ}
  -- lfp(A(·, a↑)₁)
  let aᵤᵥ := @OrderHom.lfp {x // (boundedSubtype D D1 D2 D1 ⊥ ↑aᵤ) x} CLaᵤ Aₛ

  -- ∀ x ∈ [⊥, a↑], (x, b) ≲ (x, a↑)
  have p13 : ∀ x ∈ {x | (boundedSubtype D D1 D2 D1 ⊥ ↑aᵤ) x}, (x, b) ≲ (x, aᵤ) := by
    intro x _
    apply And.intro
    .
      rfl
    .
      exact P10.2.2.1

  -- ∀ x ∈ [⊥, a↑], x ≤ b
  have p14 : ∀ x : {x // (boundedSubtype D D1 D2 D1 ⊥ ↑aᵤ) x}, x ≤ b.val :=
    λ x => O.le_trans x.val aᵤ b x.prop.2 P10.2.2.1

  -- ∀ x ∈ [⊥, a↑], A(x, b)₁ ≤ A(x, a↑)₁
  have p15 : ∀ x : {x // (boundedSubtype D D1 D2 D1 ⊥ ↑aᵤ) x}, (A ⟨(x, b), p14 x⟩).val.1 ≤ (A ⟨(x, aᵤ), x.prop.2⟩).val.1 :=
    λ x => (conA ⟨(x, b), p14 x ⟩ ⟨(x, aᵤ), x.prop.2⟩ (p13 x x.prop)).1

  -- A(·, b)₁ ≤ x
  have p16 : ∀ x : {x : Subtype (boundedSubtype D D1 D2 D1 ⊥ ↑aᵤ) // (Aₛ x) ≤ x}, (A ⟨(x, b), p14 x.val⟩).val.1 ≤ x := by
    intro x
    have notation_eq : ∀ x, Aₛ x = (A ⟨(x, aᵤ), x.prop.2⟩).val.1 := by
      intro x
      apply Subtype.ext
      exact rfl
    let r3' := p15 x.val
    rw [←notation_eq] at r3'
    exact O.le_trans (A ⟨(x, b), p14 x.val⟩).val.1 (Aₛ x) x r3' x.prop
  have p16' : ∀ x ∈ {x | Aₛ x ≤ x}, A₁ ⟨x, ⟨L1.bot_le x, O.le_trans x aᵤ b x.prop.2 P10.2.2.1⟩⟩ ≤ ⟨x, ⟨L1.bot_le x, O.le_trans x aᵤ b x.prop.2 P10.2.2.1⟩⟩ :=
    λ x x_in => p16 ⟨x, x_in⟩

  -- b↓ ∈ lowerBounds {x | A (x, b)₁ ≤ x}
  have p17 : bᵥ ∈ {x | A₁ x ≤ x} ∧ bᵥ ∈ lowerBounds {x | A₁ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype _ _ _ D1 ⊥ b) x} CLb A₁)
  -- ∀ x ∈ {x | A₁ x ≤ x}, bᵥ ≤ x
  have p17' : ∀ x ∈ {x | A₁ x ≤ x}, bᵥ ≤ x := by
    apply p17.2

  -- (a↑)↓ ∈ {x | A(x, a↑)₁ ≤ x}
  have p18 : aᵤᵥ ∈ {x | Aₛ x ≤ x} ∧ aᵤᵥ ∈ lowerBounds {x | Aₛ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype D D1 D2 D1 ⊥ aᵤ.val) x} CLaᵤ Aₛ)

  -- A ((a↑)↓, b)₁ ≤ (a↑)↓
  have p19 : A₁ ⟨aᵤᵥ, ⟨L1.bot_le aᵤᵥ, O.le_trans aᵤᵥ aᵤ b aᵤᵥ.prop.2 P10.2.2.1⟩⟩ ≤ aᵤᵥ.val := by
    exact p16' aᵤᵥ p18.1

  -- (a↑)↓ ∈ {x | A (x, b)₁ ≤ x}
  have p20 : ⟨aᵤᵥ, ⟨L1.bot_le aᵤᵥ, O.le_trans aᵤᵥ aᵤ b aᵤᵥ.prop.2 P10.2.2.1⟩⟩ ∈ {x | A₁ x ≤ x.val} := by
    exact p19

  -- Thus bᵥ ≤ aᵤᵥ
  p17' ⟨aᵤᵥ, ⟨L1.bot_le aᵤᵥ, O.le_trans aᵤᵥ aᵤ b aᵤᵥ.prop.2 P10.2.2.1⟩⟩ p20
