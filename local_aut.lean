import Final_Project.field_aut
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

set_option warningAsError false



open Matrix BigOperators
open scoped MatrixGroups

noncomputable section

/-
Part 4 of the project.

This file uses the definitions from `field_aut.lean`.  In particular it uses
`AutSL3`, `GL3`, `ringAutSL3`, `innerAutSL3byGL3`, `invTransposeAutSL3`,
and the named matrices in the namespace `FieldAutomorpisms`.

Mathematical content: after the residue-field normalization, an automorphism of
`SL₃(R)` which is congruent to the identity on the six standard generators
`d₁,d₂,d₃,w₁,w₂,x₁₂(1)` is standard over the local ring.
-/

namespace LocalAutomorphisms

variable (R : Type*) [CommRing R] [IsLocalRing R] [Invertible (2 : R)]

/-- The maximal ideal of the local ring. -/
abbrev J : Ideal R :=
  IsLocalRing.maximalIdeal R

/-- Entrywise congruence of `3 × 3` matrices modulo the maximal ideal. -/
def MatrixCongruentModJ
    (A B : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i j : Fin 3, A i j - B i j ∈ J R

/-- Congruence of elements of `SL₃(R)` modulo the maximal ideal. -/
def SLCongruentModJ (A B : SL3 R) : Prop :=
  MatrixCongruentModJ R
    (A : Matrix (Fin 3) (Fin 3) R)
    (B : Matrix (Fin 3) (Fin 3) R)

/-- Congruence of elements of `GL₃(R)` modulo the maximal ideal. -/
def GL3CongruentModJ (g h : GL3 R) : Prop :=
  MatrixCongruentModJ R
    (g : Matrix (Fin 3) (Fin 3) R)
    (h : Matrix (Fin 3) (Fin 3) R)

/-- A `GL₃(R)` element congruent to the identity modulo the maximal ideal. -/
def GL3IsOneModJ (g : GL3 R) : Prop :=
  GL3CongruentModJ R g 1

/-- An automorphism fixes a chosen `SL₃(R)` element modulo the maximal ideal. -/
def SL3FixedModJ (φ : AutSL3 R) (A : SL3 R) : Prop :=
  SLCongruentModJ R (φ A) A

/-- The three diagonal involutions are fixed modulo the maximal ideal. -/
def DiagonalFixedModJ (φ : AutSL3 R) : Prop :=
  SL3FixedModJ R φ (FieldAutomorpisms.d1SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.d2SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.d3SL R)

/-- The two signed transposition matrices are fixed modulo the maximal ideal. -/
def SignedTranspositionsFixedModJ (φ : AutSL3 R) : Prop :=
  SL3FixedModJ R φ (FieldAutomorpisms.w1SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.w2SL R)

/-- The six normalized generators are fixed modulo the maximal ideal. -/
def BasicGeneratorsFixedModJ (φ : AutSL3 R) : Prop :=
  SL3FixedModJ R φ (FieldAutomorpisms.d1SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.d2SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.d3SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.w1SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.w2SL R) ∧
  SL3FixedModJ R φ (FieldAutomorpisms.x12SL R)

/-- Exact fixation of the six normalized generators. -/
def BasicGeneratorsFixed (φ : AutSL3 R) : Prop :=
  φ (FieldAutomorpisms.d1SL R) = FieldAutomorpisms.d1SL R ∧
  φ (FieldAutomorpisms.d2SL R) = FieldAutomorpisms.d2SL R ∧
  φ (FieldAutomorpisms.d3SL R) = FieldAutomorpisms.d3SL R ∧
  φ (FieldAutomorpisms.w1SL R) = FieldAutomorpisms.w1SL R ∧
  φ (FieldAutomorpisms.w2SL R) = FieldAutomorpisms.w2SL R ∧
  φ (FieldAutomorpisms.x12SL R) = FieldAutomorpisms.x12SL R

/-- The elementary transvection `xᵢⱼ(a)` as an element of `SL₃(R)`. -/
def xijSL (i j : Fin 3) (hij : i ≠ j) (a : R) : SL3 R :=
  ⟨Matrix.transvection i j a, by
    exact Matrix.det_transvection_of_ne i j hij a⟩

/--
Entrywise congruence modulo `J` is the same as equality after reduction to the
residue field.
-/
theorem sl_congruent_iff_reduction_eq {A B : SL3 R} :
    SLCongruentModJ R A B ↔
      (Matrix.SpecialLinearGroup.map (IsLocalRing.residue R)) A =
        (Matrix.SpecialLinearGroup.map (IsLocalRing.residue R)) B := by
  sorry

/-
Lemma 3 from Block 4: if the diagonal involutions are fixed modulo `J`, then a
change of basis congruent to the identity makes them fixed exactly.
-/
theorem diagonal_preserved_after_local_change_of_basis
    (φ : AutSL3 R) (hdiag : DiagonalFixedModJ R φ) :
    ∃ g₁ : GL3 R,
      GL3IsOneModJ R g₁ ∧
      innerAutSL3byGL3 R g₁ (φ (FieldAutomorpisms.d1SL R)) = FieldAutomorpisms.d1SL R ∧
      innerAutSL3byGL3 R g₁ (φ (FieldAutomorpisms.d2SL R)) = FieldAutomorpisms.d2SL R ∧
      innerAutSL3byGL3 R g₁ (φ (FieldAutomorpisms.d3SL R)) = FieldAutomorpisms.d3SL R := by
  sorry

/-
Lemma 4 from Block 4: once the diagonal involutions are fixed exactly and the
signed transpositions are fixed modulo `J`, a diagonal change of basis congruent
to the identity fixes the signed transpositions exactly.
-/
theorem signed_transpositions_preserved_after_local_change_of_basis
    (φ : AutSL3 R)
    (hdiag_exact :
      φ (FieldAutomorpisms.d1SL R) = FieldAutomorpisms.d1SL R ∧
      φ (FieldAutomorpisms.d2SL R) = FieldAutomorpisms.d2SL R ∧
      φ (FieldAutomorpisms.d3SL R) = FieldAutomorpisms.d3SL R)
    (hw_mod : SignedTranspositionsFixedModJ R φ) :
    ∃ g₂ : GL3 R,
      GL3IsOneModJ R g₂ ∧
      innerAutSL3byGL3 R g₂ (φ (FieldAutomorpisms.d1SL R)) = FieldAutomorpisms.d1SL R ∧
      innerAutSL3byGL3 R g₂ (φ (FieldAutomorpisms.d2SL R)) = FieldAutomorpisms.d2SL R ∧
      innerAutSL3byGL3 R g₂ (φ (FieldAutomorpisms.d3SL R)) = FieldAutomorpisms.d3SL R ∧
      innerAutSL3byGL3 R g₂ (φ (FieldAutomorpisms.w1SL R)) = FieldAutomorpisms.w1SL R ∧
      innerAutSL3byGL3 R g₂ (φ (FieldAutomorpisms.w2SL R)) = FieldAutomorpisms.w2SL R := by
  sorry

/--
Lemma 5 from Block 4: after the previous normalizations, the congruence
condition on `x₁₂(1)` forces all elementary transvections with parameter `1` to
be fixed exactly.
-/
theorem transvections_one_preserved_after_local_normalization
    (φ : AutSL3 R)
    (hdiag_w_exact :
      φ (FieldAutomorpisms.d1SL R) = FieldAutomorpisms.d1SL R ∧
      φ (FieldAutomorpisms.d2SL R) = FieldAutomorpisms.d2SL R ∧
      φ (FieldAutomorpisms.d3SL R) = FieldAutomorpisms.d3SL R ∧
      φ (FieldAutomorpisms.w1SL R) = FieldAutomorpisms.w1SL R ∧
      φ (FieldAutomorpisms.w2SL R) = FieldAutomorpisms.w2SL R)
    (hx12_mod : SL3FixedModJ R φ (FieldAutomorpisms.x12SL R)) :
    ∀ i j : Fin 3, ∀ hij : i ≠ j,
      φ (xijSL R i j hij 1) = xijSL R i j hij 1 := by
  sorry

/-- A local-ring version of the predicate that an element is an elementary transvection. -/
def IsTransvectionSL3 (x : SL3 R) : Prop :=
  ∃ i j : Fin 3, ∃ hij : i ≠ j, ∃ c : R,
    x = xijSL R i j hij c

/--
Ring-level conclusion used at the end of Block 4.  If the six basic generators
are fixed, then the automorphism acts on every elementary transvection by one
ring automorphism of `R`.

This is the local-ring analogue of the final transvection step in Part 3.
-/
theorem ring_aut_from_fixed_basic_generators
    (φ : AutSL3 R) (hfixed : BasicGeneratorsFixed R φ) :
    ∃ σ : R ≃+* R,
      ∀ E : SL3 R, IsTransvectionSL3 R E →
        φ E = E.map σ := by
  sorry

/--
A standard form without the graph automorphism.  This is the normalized output
of Block 4.
-/
def IsStandardSL3AutNoGraph (φ : AutSL3 R) : Prop :=
  ∃ (σ : R ≃+* R) (g : GL3 R),
    ∀ x : SL3 R,
      φ x = ringAutSL3 R σ (innerAutSL3byGL3 R g x)

/--
The standard form used for the final theorem: inner automorphism, entrywise ring
automorphism, and possibly the graph automorphism.
-/
def IsStandardSL3Aut (φ : AutSL3 R) : Prop :=
  ∃ (σ : R ≃+* R) (ε : Bool) (g : GL3 R),
    ∀ x : SL3 R,
      φ x =
        ringAutSL3 R σ
          ((FieldAutomorpisms.graphChoiceSL3 R ε)
            (innerAutSL3byGL3 R g x))

/--
Theorem 3 / Block 4, normalized local-ring statement.

If the automorphism is congruent to the identity on
`d₁,d₂,d₃,w₁,w₂,x₁₂(1)`, then it is standard with no graph part.
-/
theorem local_class_no_graph
    (φ : AutSL3 R) (hmod : BasicGeneratorsFixedModJ R φ) :
    IsStandardSL3AutNoGraph R φ := by
  sorry

/--
The same normalized local theorem, packaged in the final standard-form predicate
by choosing `ε = false`.
-/
theorem local_class
    (φ : AutSL3 R) (hmod : BasicGeneratorsFixedModJ R φ) :
    IsStandardSL3Aut R φ := by
  rcases local_class_no_graph R φ hmod with ⟨σ, g, hσg⟩
  refine ⟨σ, false, g, ?_⟩
  intro x
  simpa [IsStandardSL3AutNoGraph, IsStandardSL3Aut,
    FieldAutomorpisms.graphChoiceSL3] using hσg x

end LocalAutomorphisms

end
