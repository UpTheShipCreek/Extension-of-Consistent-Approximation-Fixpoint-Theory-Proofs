import ThesisProofs.Imports.Defs
import ThesisProofs.Imports.Ordered_Product
import ThesisProofs.Imports.Interlattice_Properties
import ThesisProofs.Imports.Bounded_Subtype
import ThesisProofs.Imports.Consistent_Approximating_Operator
import ThesisProofs.Imports.Reliable_Pair

variable
  {D : Type u}
  {D1 D2 : D → Prop}
  [O : PartialOrder D]
  [L : BoundedPartialOrder D]
  [L1 : CompleteLatticeFromOrder (Subtype D1)]
  [L2 : CompleteLatticeFromOrder (Subtype D2)]
  (interlub : interlattice_lub D D1 D2)
  (interglb : interlattice_glb D D1 D2)
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
  (conA : consistent_approximating_operator A)
  (ab : {x // reliable A x})

def Proposition_9_A : ∀ x : {x // (boundedSubtype _ _ _ D1 L1.bot ab.1.1.2) x}, L1.bot ≤ (A ⟨(x, ab.1.1.2), x.prop.2⟩).val.1 ∧ (A ⟨(x, ab.1.1.2), x.prop.2⟩).val.1 ≤ (ab.1.1.2 : D) := by

  intro ⟨x,⟨_, x_prop⟩⟩

  let a := ab.1.1.1
  let b := ab.1.1.2

  let aₛ := L1.sSup {x | x ≤ b.val}

  -- a* ≤ b
  have p2 : ⊗(aₛ, b) :=
    interlub.2.2 b b.property {x | x ≤ b.val} (λ x x_in => x_in)

  -- ∀ x ∈ {x | x ≤ b}, (x, b) ≲ (a*, b)
  have p3 : ∀ x : {x : Subtype D1 // x ≤ b.val}, (x.val, b) ≲ (aₛ, b) := by
    intro x
    apply And.intro
    .
      exact L1.le_sSup {x | x ≤ b.val} x x.prop
    .
      rfl

  -- ∀ x ∈ {x | x ≤ b}, A (x, b) ≲ A (a*, b)
  have p4 : ∀ x : {x : Subtype D1 // x ≤ b.val}, A ⟨(x, b), x.prop⟩ ≤ A ⟨(aₛ, b), p2⟩ := by
    intro x
    exact (conA ⟨(x, b), x.prop⟩ ⟨(aₛ, b), p2⟩ (p3 x))

  -- A (a, b) ≲ A (a*, b)
  have p5: A ab ≲ (A ⟨(aₛ, b), p2⟩).val :=
    p4 ⟨a, ab.1.2⟩

  -- A (a*, b)₁ ≤ A (a, b)₂
  have p6 : (A ⟨(aₛ, b), p2⟩).val.1 ≤ (A ab).val.2.val:=
    le_trans (A ⟨(aₛ, b), p2⟩).prop p5.2

  -- A (a, b)₂ ≤ b
  have p7 : (A ab).val.2.val ≤ b.val :=
    ab.prop.2

  -- ∀ x ∈ {x | x ≤ b}, A (x, b)₁ ≤ A (a*, b)₁
  have p8 : (A ⟨(x, b), x_prop⟩).val.1 ≤ (A ⟨(aₛ, b), p2⟩).val.1 :=
    (p4 ⟨x, x_prop⟩).1

  -- ∀ x ∈ {x | x ≤ b}, A (x, b)₁ ≤ A (a, b)₂
  have p9 := O.le_trans (A ⟨(x, b), x_prop⟩).val.1 (A ⟨(aₛ, b), p2⟩).val.1 (A ab).val.2.val p8 p6

  -- ∀ x ∈ {x | x ≤ b}, A (x, b)₁ ≤ b
  have p10 := O.le_trans (A ⟨(x, b), x_prop⟩).val.1 (A ab).val.2.val b.val  p9 p7

  -- Thus ⊥ ≤ A (x, b)₁ ≤ b
  exact ⟨L1.bot_le (A ⟨(x, b), x_prop⟩).val.1, p10⟩


def Proposition_9_B : ∀ x : {x // (boundedSubtype _ _ _ D2 ab.1.1.1 L2.top) x}, ab.1.1.1 ≤ (A ⟨(ab.1.1.1, x), x.prop.1⟩).val.2.val ∧ (A ⟨(ab.1.1.1, x), x.prop.1⟩).val.2.val ≤ (L2.top : D) := by

  intro ⟨x, ⟨x_prop, _⟩⟩

  let a := ab.1.1.1
  let b := ab.1.1.2

  let bₛ := L2.sInf {x | a ≤ x.val}

  -- a ≤ b*
  have s2 : ⊗(a, bₛ) :=
    interglb.2.2 a a.property {x | a ≤ x.val} (λ x x_in => x_in)

  -- ∀ x ∈ {x | a ≤ x}, (a, x) ≲ (a, b*)
  have s3 : ∀ x : {x : Subtype D2 // a.val ≤ x}, (a, x.val) ≲ (a, bₛ) := by
    intro x
    apply And.intro
    .
      rfl
    .
      exact L2.sInf_le {x | a.val ≤ x} x x.prop

  -- ∀ x ∈ {x | a ≤ x}, A (a, x) ≲ A (a, b*)
  have s4 : ∀ x : {x : Subtype D2 // a.val ≤ x}, (A ⟨(a, x), x.prop⟩) ≤ (A ⟨(a, bₛ), s2⟩)  := by
    intro x
    exact (conA ⟨(a, x), x.prop⟩ ⟨(a, bₛ), s2⟩ (s3 x))

  -- A (a, b) ≲ A (a, b*)
  have s5 : A ab ≲ (A ⟨(a, bₛ), s2⟩).val :=
    s4 ⟨b, ab.1.2⟩

  -- a ≤ A (a, b)₁
  have s6 : a ≤ (A ab).val.1:=
    ab.prop.1

  -- A (a, b)₁ ≤ A (a, b*)₂
  have s7 := O.le_trans (A ab).val.1 (A ⟨(a, bₛ), s2⟩).val.1 (A ⟨(a, bₛ), s2⟩).val.2 s5.1 (A ⟨(a, bₛ), s2⟩).prop

  -- ∀ x ∈ {x | a ≤ x}, A (a, b)₁ ≤ A(a, x)₂
  have s8 := O.le_trans (A ab).val.1 (A ⟨(a, bₛ), s2⟩).val.2.val (A ⟨(a, x), x_prop⟩).val.2.val s7 (s4 ⟨x, x_prop⟩).2

  -- ∀ x ∈ {x | a ≤ x}, a ≤ A (a, x)₂
  have s9 := O.le_trans a (A ab).val.1 (A ⟨(a, x), x_prop⟩).val.2 s6 s8

  -- Thus a ≤ A (a, x)₂ ≤ ⊤
  exact ⟨s9, L2.le_top (A ⟨(a, x), x_prop⟩).val.2⟩
