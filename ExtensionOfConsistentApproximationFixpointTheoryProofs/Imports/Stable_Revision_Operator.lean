import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Ordered_Product
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Interlattice_Properties
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Bounded_Subtype
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Consistent_Approximating_Operator
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Reliable_Pair

import ExtensionOfConsistentApproximationFixpointTheoryProofs.Propositions.Proposition_8
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Propositions.Proposition_9


variable
  {D : Type u}
  {D1 D2 : D → Prop}
  [PartialOrder D]
  [BoundedPartialOrder D]
  [L1 : CompleteLatticeFromOrder (Subtype D1)]
  [L2 : CompleteLatticeFromOrder (Subtype D2)]
  (interglb : interlattice_glb D D1 D2)
  (interlub : interlattice_lub D D1 D2)
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
  (conA : consistent_approximating_operator A)
  (ab : {x // reliable A x})

def A₁Partial : Subtype (boundedSubtype _ _ _ D1 L1.bot ab.1.1.2) → Subtype (boundedSubtype _ _ _ D1 L1.bot ab.1.1.2) :=
  λ x => ⟨(A ⟨(x, ab.1.1.2), x.prop.2⟩).val.1, Proposition_9_A interlub A conA ab x⟩

def A₂Partial : Subtype (boundedSubtype _ _ _ D2 ab.1.1.1 L2.top) → Subtype (boundedSubtype _ _ _ D2 ab.1.1.1 L2.top) :=
  λ x => ⟨(A ⟨(ab.1.1.1, x), x.prop.1⟩).val.2, Proposition_9_B interglb A conA ab x⟩

def A₁Monotone : Monotone (A₁Partial interlub A conA ab) :=
  let b := ab.1.1.2

  λ ⟨d1, od1⟩  ⟨d2, od2⟩ hle =>
    have les_inf : ⟨d1, b⟩ ≲ ⟨d2, b⟩ := by
      apply And.intro
      ·
        exact hle
      ·
        rfl
    (conA ⟨(d1,b), od1.2⟩ ⟨(d2,b), od2.2⟩ les_inf).1

def A₂Monotone : Monotone (A₂Partial interglb A conA ab) :=
  let a := ab.1.1.1

  λ ⟨d1, od1⟩ ⟨d2, od2⟩ hle =>
    have les_inf : ⟨a, d2⟩ ≲ ⟨a, d1⟩ := by
      apply And.intro
      ·
        rfl
      ·
        exact hle
    (conA ⟨(a, d2), od2.1⟩ ⟨(a, d1), od1.1⟩ les_inf).2

def A₁OrderHom : OrderHom (Subtype (boundedSubtype _ _ _ D1 L1.bot ab.1.1.2)) (Subtype (boundedSubtype _ _ _ D1 L1.bot ab.1.1.2)) :=
  {
    toFun := A₁Partial interlub A conA ab
    monotone' := A₁Monotone interlub A conA ab
  }

def A₂OrderHom : OrderHom (Subtype (boundedSubtype _ _ _ D2 ab.1.1.1 L2.top)) (Subtype (boundedSubtype _ _ _ D2 ab.1.1.1 L2.top)) :=
  {
    toFun := A₂Partial interglb A conA ab
    monotone' := A₂Monotone interglb A conA ab
  }

-- notation b↓
def rOb : Subtype (boundedSubtype _ _ _ D1 L1.bot ab.1.1.2) :=
  let b := ab.1.1.2

  @OrderHom.lfp
  {x // (boundedSubtype _ _ _ D1 L1.bot b) x}
  (Proposition_8_A b interlub)
  (A₁OrderHom interlub A conA ab)

-- notation a↑
def rOa : {x // (boundedSubtype _ _ _ D2 ab.1.1.1 L2.top) x} :=
  let a := ab.1.1.1

  @OrderHom.lfp
  {x // (boundedSubtype _ _ _ D2 a L2.top) x}
  (Proposition_8_B a interglb)
  (A₂OrderHom interglb A conA ab)
