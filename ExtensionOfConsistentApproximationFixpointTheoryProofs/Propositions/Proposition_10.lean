import ThesisProofs.Imports.Defs
import ThesisProofs.Imports.Ordered_Product
import ThesisProofs.Imports.Interlattice_Properties
import ThesisProofs.Imports.Bounded_Subtype
import ThesisProofs.Imports.Consistent_Approximating_Operator
import ThesisProofs.Imports.Reliable_Pair
import ThesisProofs.Imports.Stable_Revision_Operator

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
  (ab : {x // reliable A x})

def Proposition_10  :
(rOb interlub A conA ab) ≤ ab.1.1.2.val ∧
ab.1.1.1.val ≤ (rOa interglb A conA ab) ∧
(rOa interglb A conA ab) ≤ ab.1.1.2.val ∧
(rOb interlub A conA ab) ≤ (rOa interglb A conA ab).val.val := by

  let a := ab.1.1.1
  let b := ab.1.1.2

  let A₁ := A₁OrderHom interlub A conA ab
  let A₂ := A₂OrderHom interglb A conA ab

  let bᵥ := (rOb interlub A conA ab)
  let aᵤ := (rOa interglb A conA ab)

  -- a↑ ∈ lowerBounds {x | A₂ x ≤ x}
  have p1 : aᵤ ∈ {x | A₂ x ≤ x} ∧ aᵤ ∈ lowerBounds {x | A₂ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype D D1 D2 D2 a L2.top) x} (Proposition_8_B a interglb) A₂)

  -- b ∈ {x | A₂ x ≤ x}
  have p2 : ⟨b, ⟨ab.1.2, L2.le_top b⟩⟩ ∈ {x | A₂ x ≤ x} := by
    let Aab2_le_b : (A ab).val.2 ≤ b := ab.prop.2
    -- Need to prove that (A (a, b)).2 = A₂ b
    have A2b_le_b : (A ab).val.2 = A₂ ⟨b, ⟨ab.1.2, L2.le_top b⟩⟩ := by
      apply Subtype.ext
      exact rfl
    rw [A2b_le_b] at Aab2_le_b
    simp
    exact Aab2_le_b

  -- a↑ ≤ b (since a↑ is in the lower bounds of the prefixpoints of A₂)
  have p3 : aᵤ ≤ b.val := by
    have aᵤ_lb := p1.2
    have aᵤ_le : ∀ x, x ∈ {x | A₂ x ≤ x} → aᵤ ≤ x := by
      apply aᵤ_lb
    exact aᵤ_le ⟨b, ⟨ab.1.2, L2.le_top b⟩⟩ p2

  let aₛ := L1.sSup {x | x.val ≤ aᵤ}

  -- a ∈ {x | x ≤ a↑}
  have p5 : a ∈ {x : {x // D1 x} | x.val ≤ aᵤ} := by
    apply aᵤ.prop.1

  -- a ≤ a*
  have p6 : a.val ≤ aₛ := by
    exact L1.le_sSup {x | x.val ≤ aᵤ} a p5

  -- a* ≤ a↑
  have p7 : aₛ.val ≤ aᵤ :=
    interlub.2.2 aᵤ aᵤ.val.prop {x | x.val ≤ aᵤ} (λ x x_in => x_in)

  -- a* ≤ b
  have p8 : aₛ ≤ b.val :=
    O.le_trans aₛ aᵤ b p7 p3

  -- (a*, b) ≲ (a*, a↑)
  have p9 : (aₛ, b) ≲ (aₛ, ↑aᵤ) := by
      apply And.intro
      .
        rfl
      .
        exact p3

  -- A (a*, b) ≲ A (a*, a↑)
  have p10 : A ⟨(aₛ, b), p8⟩ ≲ (A ⟨(aₛ, aᵤ), p7⟩).val :=
    conA ⟨(aₛ, b),p8⟩  ⟨(aₛ, aᵤ),p7⟩ p9

  -- (a, a↑) ≲ (a*, a↑)
  have p11 : (a, aᵤ) ≲ (aₛ, aᵤ) := by
      apply And.intro
      .
        apply p6
      .
        rfl

  -- A (a, a↑) ≲ A (a*, a↑)
  have p12 : A ⟨(a, aᵤ), aᵤ.prop.1⟩ ≲ (A ⟨(aₛ, aᵤ), p7⟩).val :=
    conA ⟨(a, aᵤ),aᵤ.prop.1⟩  ⟨(aₛ, aᵤ), p7⟩ p11

  -- A (a*, b)₁ ≤ A (a*, a↑)₂
  have p13 : (A ⟨(aₛ, b), p8⟩).val.1 ≤ (A ⟨(aₛ, aᵤ), p7⟩).val.2.val :=
    O.le_trans (A ⟨(aₛ, b), p8⟩).val.1.val (A ⟨(aₛ, aᵤ), p7⟩).val.1.val (A ⟨(aₛ, aᵤ), p7⟩).val.2.val p10.1 (A ⟨(aₛ, aᵤ), p7⟩).prop

  -- A (a*, b)₁ ≤ A (a, a↑)₂
  have p14 : (A ⟨(aₛ, b), p8⟩).val.1 ≤ (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2.val :=
    O.le_trans (A ⟨(aₛ, b), p8⟩).val.1.val (A ⟨(aₛ, aᵤ), p7⟩).val.2.val (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2.val p13 p12.2

  -- A (a, a↑)₂ = a↑
  have p15 : A₂ aᵤ = aᵤ :=
    @OrderHom.map_lfp {x // (boundedSubtype _ _ _ D2 a ⊤) x} (Proposition_8_B a interglb) A₂
  have p15' : A₂ aᵤ = (A ⟨(a, aᵤ), aᵤ.prop.1⟩).val.2 := by
    tauto

  -- A(a*, b)₁ ≤ a↑
  have p16 : (A ⟨(aₛ, b), p8⟩).val.1.val ≤ aᵤ := by
    rw [←p15', p15] at p14
    exact p14

  -- A(a*, b)₁ ∈ {x ∈ L₁ | x ≤ a↑}
  have p17 : (A ⟨(aₛ, b), p8⟩).val.1 ∈ {x : {x // D1 x} | x.val ≤ aᵤ} := p16

  -- A(a*, b)₁ ≤ a*
  have p18 :  (A ⟨(aₛ, b), p8⟩).val.1 ≤ aₛ :=
    L1.le_sSup {x | x.val ≤ aᵤ} (A ⟨(aₛ, b), p8⟩).val.1 p17

  -- a* ∈ {x | A(x, b)₁ ≤ x}
  have p19 : ⟨aₛ, ⟨L1.bot_le aₛ , p8⟩⟩ ∈ {x | A₁ x ≤ x} := by
    have notational_eq : ∀ x, A₁ x = (A ⟨(x, b), x.prop.2⟩).val.1 := by
      intro x
      apply Subtype.ext
      exact rfl
    have proof : A₁ ⟨aₛ, ⟨L1.bot_le aₛ , p8⟩⟩ ≤ aₛ := by
      rw [notational_eq]
      exact p18
    exact proof

  -- b↓ ∈ lowerBounds {x | A(x, b)₁ ≤ x}
  have p20 : bᵥ ∈ {x | A₁ x ≤ x} ∧ bᵥ ∈ lowerBounds {x | A₁ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype D D1 D2 D1 ⊥ b) x} (Proposition_8_A b interlub) A₁)

  -- ∀ x, x ∈ {x | A(x, b)₁ ≤ x}, b↓ ≤ x
  have p20' : ∀ x, x ∈ {x | A₁ x ≤ x} → bᵥ ≤ x := by
    apply p20.2

  -- b↓ ≤ a*
  have p21 : bᵥ ≤ aₛ := by
    exact p20' ⟨aₛ, ⟨L1.bot_le aₛ , p8⟩⟩ p19

  -- b↓ ≤ b
  have p22 := O.le_trans bᵥ aₛ b p21 p8

  -- a ≤ a↑
  have p23 := aᵤ.prop.1

  -- a↑ ≤ b
  have p24 := p3

  -- b↓ ≤ a↑
  have p25 := O.le_trans bᵥ aₛ aᵤ p21 p7

  exact ⟨p22, p23, p24, p25⟩
