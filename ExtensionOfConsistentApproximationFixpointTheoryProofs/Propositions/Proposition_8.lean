import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Interlattice_Properties
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Bounded_Subtype

variable
  {D : Type u}
  {D1 D2 : D → Prop}
  [PartialOrder D]
  [L : BoundedPartialOrder D]
  [L1 : CompleteLatticeFromOrder (Subtype D1)]
  [L2 : CompleteLatticeFromOrder (Subtype D2)]
  (a : Subtype D1)
  (b : Subtype D2)
  (interlub : interlattice_lub D D1 D2)
  (interglb : interlattice_glb D D1 D2)


def sSupBoundedIsInBounds_L1 (S : Set (Subtype (boundedSubtype _ _ _ D1 L1.bot b))) :
(boundedSubtype _ _ _ D1 L1.bot b) (L1.sSup (Subtype.val '' S)) := by
  apply And.intro
  ·
    apply L1.bot_le
  ·
    exact interlub.2.2 b b.property (Subtype.val '' S) (λ x ⟨x', ⟨_, x'eqx⟩⟩ => x'eqx ▸ x'.prop.2)

instance CompleteSemilatticeSupBoundedSubtype_L1 : CompleteSemilatticeSup ({x // (boundedSubtype _ _ _ D1 L1.bot b) x}) :=
  {
    le := λ x y => (x : D) ≤ (y : D)
    lt := λ x y => (x : D) < (y : D)
    le_refl := λ x => L1.le_refl x
    le_trans := λ x y z => L1.le_trans x y z
    lt_iff_le_not_le := λ x y => L1.lt_iff_le_not_le x y
    le_antisymm := λ x y hxy hyx => Subtype.ext (L1.le_antisymm x.val y.val hxy hyx)
    sSup := λ s => ⟨L1.sSup (Subtype.val '' s), sSupBoundedIsInBounds_L1 b interlub s⟩
    le_sSup := λ s x hx => L1.le_sSup (Subtype.val '' s) x ⟨x, hx, rfl⟩
    sSup_le := λ s x ub => L1.sSup_le (Subtype.val '' s) x (λ _ ⟨x, x_in_s, x_eq_b⟩ => x_eq_b ▸ ub x x_in_s)
  }

def Proposition_8_A : (CompleteLattice {x // (boundedSubtype _ _ _ D1 L1.bot b) x}) :=
  @completeLatticeOfCompleteSemilatticeSup
  {x // (boundedSubtype _ _ _ D1 L1.bot b) x}
  (CompleteSemilatticeSupBoundedSubtype_L1 b interlub)

def sInfBoundedIsInBounds_L2 (S : Set (Subtype (boundedSubtype _ _ _ D2 a L2.top))) : (boundedSubtype _ _ _ D2 a L2.top) (L2.sInf (Subtype.val '' S)) := by
  apply And.intro
  ·
    exact interglb.2.2 a a.prop (Subtype.val '' S) (λ x ⟨x', ⟨_, x'eqx⟩⟩ => x'eqx ▸ x'.prop.1)
  ·
    apply L2.le_top

instance CompleteSemilatticeInfBoundedSubtype_L2 : CompleteSemilatticeInf ({x // (boundedSubtype _ _ _ D2 a L2.top) x}) :=
  {
    le := λ x y => (x : D) ≤ (y : D)
    lt := λ x y => (x : D) < (y : D)
    le_refl := λ x => L2.le_refl x
    le_trans := λ x y z => L2.le_trans x y z
    lt_iff_le_not_le := λ x y => L2.lt_iff_le_not_le x y
    le_antisymm := λ x y hxy hyx => Subtype.ext (L2.le_antisymm x.val y.val hxy hyx)
    sInf := λ s => ⟨L2.sInf (Subtype.val '' s), sInfBoundedIsInBounds_L2 a interglb s⟩
    sInf_le := λ s x hx => L2.sInf_le (Subtype.val '' s) x ⟨x, hx, rfl⟩
    le_sInf := λ s x ub => L2.le_sInf (Subtype.val '' s) x (λ _ ⟨x, x_in_s, x_eq_b⟩ => x_eq_b ▸ ub x x_in_s)
  }

def Proposition_8_B : (CompleteLattice {x // (boundedSubtype _ _ _ D2 a L2.top) x}) :=
  @completeLatticeOfCompleteSemilatticeInf
  {x // (boundedSubtype _ _ _ D2 a L2.top) x}
  (CompleteSemilatticeInfBoundedSubtype_L2 a interglb)
