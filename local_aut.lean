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
  constructor
  · intro h
    ext i j
    exact (Ideal.Quotient.eq (I := J R) (x := A i j) (y := B i j)).2 (h i j)
  · intro h i j 
    have h' :
        (IsLocalRing.residue R) (A i j) = (IsLocalRing.residue R) (B i j) := by
      simpa [Matrix.SpecialLinearGroup.map] using
        congrArg
          (fun X : SL3 (IsLocalRing.ResidueField R) =>
            (X : Matrix (Fin 3) (Fin 3) (IsLocalRing.ResidueField R)) i j) h
    exact (Ideal.Quotient.eq (I := J R) (x := A i j) (y := B i j)).1 h'

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
  let τ1 : Matrix (Fin 3) (Fin 3) R := φ (FieldAutomorpisms.d1SL R)
  let τ2 : Matrix (Fin 3) (Fin 3) R := φ (FieldAutomorpisms.d2SL R)
  let τ3 : Matrix (Fin 3) (Fin 3) R := φ (FieldAutomorpisms.d3SL R)
  let d1m : Matrix (Fin 3) (Fin 3) R := FieldAutomorpisms.d1SL R
  let d2m : Matrix (Fin 3) (Fin 3) R := FieldAutomorpisms.d2SL R
  let d3m : Matrix (Fin 3) (Fin 3) R := FieldAutomorpisms.d3SL R
  let two_inv : R := ⅟2
  -- Construct the first transition matrix U directly
  let U : Matrix (Fin 3) (Fin 3) R := two_inv • (1 + τ1 * d1m)
  -- Prove τ1 is an involution (τ1 * τ1 = 1) because φ is a group homomorphism
  have ht1_sq : τ1 * τ1 = 1 := by
    have h_mul : τ1 * τ1 = ↑(φ (FieldAutomorpisms.d1SL R) * φ (FieldAutomorpisms.d1SL R)) := rfl
    rw [h_mul]
    rw [← map_mul]
    have hd1 : FieldAutomorpisms.d1SL R * FieldAutomorpisms.d1SL R = 1 := by
      apply Subtype.ext
      change FieldAutomorpisms.d1 R * FieldAutomorpisms.d1 R = 1
      dsimp [FieldAutomorpisms.d1]
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        fin_cases i <;> simp
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    rw [hd1]
    rw [map_one φ]
    rfl
  have hd1_sq : d1m * d1m = 1 := by
    dsimp [d1m]
    change FieldAutomorpisms.d1 R * FieldAutomorpisms.d1 R = 1
    dsimp[FieldAutomorpisms.d1]
    rw[Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      fin_cases i <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  -- Prove U diagonalizes τ1
  have ht1U_eq_Ud1 : τ1 * U = U * d1m := by
    change τ1 * (two_inv • (1 + τ1 * d1m)) = (two_inv • (1 + τ1 * d1m)) * d1m
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, add_mul]
    rw [mul_one, one_mul]
    rw [← mul_assoc τ1 τ1 d1m, mul_assoc τ1 d1m d1m]
    rw [ht1_sq, hd1_sq]
    rw [one_mul, mul_one]
    exact add_comm τ1 d1m
  -- Prove U is congruent to 1 mod J
  have hU_mod_J : MatrixCongruentModJ R U 1 := by
    -- MatrixCongruentModJ means ∀ i j, U i j - 1 i j ∈ J R
    intro i j
    -- We want to show U i j - 1 i j = two_inv * ∑ k, (τ1 i k - d1m i k) * d1m k j
    have h_eq : U i j - (1 : Matrix (Fin 3) (Fin 3) R) i j =
        two_inv * (∑ k : Fin 3, (τ1 i k - d1m i k) * d1m k j) := by
      have h_half (a b : R) : two_inv * (a + b) - a = two_inv * (b - a) := by
        have h_two : two_inv * (2 : R) = 1 := invOf_mul_self (2 : R)
        calc
          two_inv * (a + b) - a = two_inv * (a + b) - 1 * a := by rw [one_mul]
          _ = two_inv * (a + b) - (two_inv * 2) * a := by rw [h_two]
          _ = two_inv * (b - a) := by ring
      change two_inv * ((1 : Matrix (Fin 3) (Fin 3) R) i j + (τ1 * d1m) i j) -
        (1 : Matrix (Fin 3) (Fin 3) R) i j = _
      have h_step := h_half ((1 : Matrix (Fin 3) (Fin 3) R) i j) ((τ1 * d1m) i j)
      rw [h_step]
      have h1 : (1 : Matrix (Fin 3) (Fin 3) R) i j = (d1m * d1m) i j := by rw [← hd1_sq]
      rw [h1]
      simp only [Matrix.mul_apply]
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_eq]
    have h_sum : (∑ k : Fin 3, (τ1 i k - d1m i k) * d1m k j) ∈ J R := by
      apply (J R).sum_mem
      intro k _
      apply (J R).mul_mem_right (d1m k j)
      exact hdiag.1 i k
    exact (J R).mul_mem_left two_inv h_sum
  -- Because U ≡ 1 mod J, its determinant is ≡ 1 mod J, hence a unit.
  -- This allows you to lift U to GL3(R)
  have hU_isUnit : IsUnit (U.det) := by
    let π := IsLocalRing.residue R
    have h_map_U : U.map π = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      have h_quot : π (U i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j) :=
        (Ideal.Quotient.eq (I := J R) (x := U i j) (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)).mpr
        (hU_mod_J i j)
      rw [h_quot]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    -- The determinant of U maps to the determinant of the identity matrix
    have h_det_map : π U.det = 1 := by
      calc
        π U.det = (U.map π).det := (RingHom.map_det π U).symm
        _ = (1 : Matrix (Fin 3) (Fin 3) _).det := by rw [h_map_U]
        _ = 1 := Matrix.det_one
    have h_unit_pi : IsUnit (π U.det) := by
      rw [h_det_map]
      exact isUnit_one
    -- Because π(U.det) is a unit in the residue field, U.det is a unit in R.
    exact isUnit_of_map_unit π U.det h_unit_pi
  let U_GL : GL3 R := Matrix.nonsingInvUnit U hU_isUnit
  -- repeat the process for τ2 in the new basis
  let U_val : Matrix (Fin 3) (Fin 3) R := ↑U_GL
  let U_inv : Matrix (Fin 3) (Fin 3) R := ↑(U_GL⁻¹)
  let τ2_prime : Matrix (Fin 3) (Fin 3) R := U_inv * τ2 * U_val
  -- Define V analogously to U
  let V : Matrix (Fin 3) (Fin 3) R := two_inv • (1 + τ2_prime * d2m)
  have ht2_sq : τ2 * τ2 = 1 := by
      have h_mul : τ2 * τ2 = ↑(φ (FieldAutomorpisms.d2SL R) * φ (FieldAutomorpisms.d2SL R)) := rfl
      rw [h_mul, ← map_mul]
      have hd2 : FieldAutomorpisms.d2SL R * FieldAutomorpisms.d2SL R = 1 := by
        apply Subtype.ext
        change FieldAutomorpisms.d2 R * FieldAutomorpisms.d2 R = 1
        dsimp [FieldAutomorpisms.d2]
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases h : i = j
        · subst h
          simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
          fin_cases i <;> simp
        · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rw [hd2, map_one]
      rfl
  have ht2_prime_sq : τ2_prime * τ2_prime = 1 := by
    dsimp [τ2_prime]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U_val U_inv (τ2 * U_val)]
    have h_U_mul_inv : U_val * U_inv = 1 := by
      dsimp [U_val, U_inv]
      exact Units.mul_inv U_GL
    rw [h_U_mul_inv]
    rw [Matrix.one_mul]
    rw [← Matrix.mul_assoc τ2 τ2 U_val]
    rw [ht2_sq]
    rw [Matrix.one_mul]
    dsimp [U_inv, U_val]
    exact Units.inv_mul U_GL
  have hd2_sq : d2m * d2m = 1 := by
    -- same proof structure as hd1_sq
    dsimp [d2m]
    change FieldAutomorpisms.d2 R * FieldAutomorpisms.d2 R = 1
    dsimp[FieldAutomorpisms.d2]
    rw[Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      fin_cases i <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have ht2primeV_eq_Vd2 : τ2_prime * V = V * d2m := by
    change τ2_prime * (two_inv • (1 + τ2_prime * d2m)) = (two_inv • (1 + τ2_prime * d2m)) * d2m
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, add_mul]
    rw [mul_one, one_mul]
    rw [← mul_assoc τ2_prime τ2_prime d2m, mul_assoc τ2_prime d2m d2m]
    rw [ht2_prime_sq, hd2_sq]
    rw [one_mul, mul_one]
    exact add_comm τ2_prime d2m
  have hd1_t2prime_comm : d1m * τ2_prime = τ2_prime * d1m := by
    have ht1_t2_comm : τ1 * τ2 = τ2 * τ1 := by
      have h_mul1 : τ1 * τ2 = ↑(φ (FieldAutomorpisms.d1SL R) * φ (FieldAutomorpisms.d2SL R)) := rfl
      have h_mul2 : τ2 * τ1 = ↑(φ (FieldAutomorpisms.d2SL R) * φ (FieldAutomorpisms.d1SL R)) := rfl
      rw [h_mul1, h_mul2, ← map_mul, ← map_mul]
      have hd1d2 : FieldAutomorpisms.d1SL R * FieldAutomorpisms.d2SL R =
                   FieldAutomorpisms.d2SL R * FieldAutomorpisms.d1SL R := by
        apply Subtype.ext
        change FieldAutomorpisms.d1 R * FieldAutomorpisms.d2 R = FieldAutomorpisms.d2 R *
        FieldAutomorpisms.d1 R
        dsimp [FieldAutomorpisms.d1, FieldAutomorpisms.d2]
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases h : i = j
        · subst h; simp only [Matrix.diagonal_apply_eq]; ring
        · simp [Matrix.diagonal_apply_ne _ h]
      rw [hd1d2]
    have hU_d1 : U_val * d1m = τ1 * U_val := ht1U_eq_Ud1.symm
    have hd1_Uinv : d1m * U_inv = U_inv * τ1 := by
      have h_inv_mul : U_inv * U_val = 1 := by exact Units.inv_mul U_GL
      have h_mul_inv : U_val * U_inv = 1 := by exact Units.mul_inv U_GL
      have h1 : d1m * U_inv = 1 * (d1m * U_inv) := by rw [Matrix.one_mul]
      rw [h1]
      rw [← h_inv_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U_val d1m U_inv]
      rw [hU_d1]
      simp only [Matrix.mul_assoc]
      rw [h_mul_inv]
      rw [Matrix.mul_one]
    dsimp [τ2_prime]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d1m U_inv (τ2 * U_val)]
    rw [hd1_Uinv]
    rw [Matrix.mul_assoc U_inv τ1 (τ2 * U_val)]
    rw [← Matrix.mul_assoc τ1 τ2 U_val]
    rw [ht1_t2_comm]
    rw [Matrix.mul_assoc τ2 τ1 U_val]
    rw [← hU_d1]
  have hd1_V_comm : d1m * V = V * d1m := by
    have hd1d2_comm : d1m * d2m = d2m * d1m := by
      dsimp [d1m, d2m]
      change FieldAutomorpisms.d1 R * FieldAutomorpisms.d2 R = FieldAutomorpisms.d2 R *
      FieldAutomorpisms.d1 R
      dsimp [FieldAutomorpisms.d1, FieldAutomorpisms.d2]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    change d1m * (two_inv • (1 + τ2_prime * d2m)) = (two_inv • (1 + τ2_prime * d2m)) * d1m
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, add_mul]
    rw [mul_one, one_mul]
    rw [← Matrix.mul_assoc d1m τ2_prime d2m]
    rw [hd1_t2prime_comm]
    rw [Matrix.mul_assoc τ2_prime d1m d2m]
    rw [hd1d2_comm]
    rw [← Matrix.mul_assoc τ2_prime d2m d1m]
  have hV_mod_J : MatrixCongruentModJ R V 1 := by
    let π := IsLocalRing.residue R
    have h_map_U : U_val.map π = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      have h_quot : π (U_val i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j) :=
        (Ideal.Quotient.eq (I := J R) (x := U_val i j)
        (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)).mpr (hU_mod_J i j)
      rw [h_quot]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_map_one : (1 : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π 
    have h_map_U_inv : U_inv.map π = 1 := by
      have h_inv : U_inv * U_val = 1 := Units.inv_mul U_GL
      have h_map_inv : (U_inv * U_val).map π = (1 : Matrix (Fin 3) (Fin 3) R).map π := by rw [h_inv]
      rw [Matrix.map_mul] at h_map_inv
      rw [h_map_U] at h_map_inv
      rw [Matrix.mul_one] at h_map_inv
      rw [h_map_one] at h_map_inv
      exact h_map_inv
    have h_map_t2 : τ2.map π = d2m.map π := by
      ext i j
      simp only [Matrix.map_apply]
      exact (Ideal.Quotient.eq (I := J R) (x := τ2 i j) (y := d2m i j)).mpr (hdiag.2.1 i j)
    have h_map_t2_prime : τ2_prime.map π = d2m.map π := by
      dsimp [τ2_prime]
      rw [Matrix.map_mul, Matrix.map_mul]
      rw [h_map_U_inv, h_map_U, h_map_t2]
      rw [Matrix.one_mul, Matrix.mul_one]
    have ht2_prime_mod_J : MatrixCongruentModJ R τ2_prime d2m := by
      intro i j
      have h_eq := congr_fun (congr_fun h_map_t2_prime i) j
      simp only [Matrix.map_apply] at h_eq
      exact (Ideal.Quotient.eq (I := J R) (x := τ2_prime i j) (y := d2m i j)).mp h_eq
    intro i j
    have h_eq : V i j - (1 : Matrix (Fin 3) (Fin 3) R) i j =
        two_inv * (∑ k : Fin 3, (τ2_prime i k - d2m i k) * d2m k j) := by
      have h_half (a b : R) : two_inv * (a + b) - a = two_inv * (b - a) := by
        have h_two : two_inv * (2 : R) = 1 := invOf_mul_self (2 : R)
        calc
          two_inv * (a + b) - a = two_inv * (a + b) - 1 * a := by rw [one_mul]
          _ = two_inv * (a + b) - (two_inv * 2) * a := by rw [h_two]
          _ = two_inv * (b - a) := by ring
      change two_inv * ((1 : Matrix (Fin 3) (Fin 3) R) i j + (τ2_prime * d2m) i j) -
        (1 : Matrix (Fin 3) (Fin 3) R) i j = _
      have h_step := h_half ((1 : Matrix (Fin 3) (Fin 3) R) i j) ((τ2_prime * d2m) i j)
      rw [h_step]
      have h1 : (1 : Matrix (Fin 3) (Fin 3) R) i j = (d2m * d2m) i j := by rw [← hd2_sq]
      rw [h1]
      simp only [Matrix.mul_apply]
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_eq]
    have h_sum : (∑ k : Fin 3, (τ2_prime i k - d2m i k) * d2m k j) ∈ J R := by
      apply (J R).sum_mem
      intro k _
      apply (J R).mul_mem_right (d2m k j)
      exact ht2_prime_mod_J i k
    exact (J R).mul_mem_left two_inv h_sum
  have hV_isUnit : IsUnit (V.det) := by
    let π := IsLocalRing.residue R
    have h_map_V : V.map π = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      have h_quot : π (V i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j) :=
        (Ideal.Quotient.eq (I := J R) (x := V i j)
        (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)).mpr (hV_mod_J i j)
      rw [h_quot]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_det_map : π V.det = 1 := by
      calc
        π V.det = (V.map π).det := (RingHom.map_det π V).symm
        _ = (1 : Matrix (Fin 3) (Fin 3) _).det := by rw [h_map_V]
        _ = 1 := Matrix.det_one
    have h_unit_pi : IsUnit (π V.det) := by
      rw [h_det_map]
      exact isUnit_one
    exact isUnit_of_map_unit π V.det h_unit_pi
  let V_GL : GL3 R := Matrix.nonsingInvUnit V hV_isUnit
  -- final transition matrix P and witness g₁
  let P_GL : GL3 R := U_GL * V_GL
  let g1 : GL3 R := P_GL⁻¹
  have hg1_mod_J : GL3IsOneModJ R g1 := by
    intro i j
    let π := IsLocalRing.residue R
    have h_quot := Ideal.Quotient.eq (I := J R) (x := (↑g1 : Matrix (Fin 3) (Fin 3) R) i j)
      (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)
    apply h_quot.mp
    have h_map_U : U_val.map π = 1 := by
      ext x y
      simp only [Matrix.map_apply]
      have hq : π (U_val x y) = π ((1 : Matrix (Fin 3) (Fin 3) R) x y) :=
        (Ideal.Quotient.eq (I := J R) (x := U_val x y)
        (y := (1 : Matrix (Fin 3) (Fin 3) R) x y)).mpr (hU_mod_J x y)
      rw [hq]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_map_V : V.map π = 1 := by
      ext x y
      simp only [Matrix.map_apply]
      have hq : π (V x y) = π ((1 : Matrix (Fin 3) (Fin 3) R) x y) :=
        (Ideal.Quotient.eq (I := J R) (x := V x y) (y := (1 : Matrix (Fin 3) (Fin 3) R) x y)).mpr
        (hV_mod_J x y)
      rw [hq]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_map_one : (1 : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      ext x y
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_P_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := Units.val_mul U_GL V_GL
    have h_map_P : (↑P_GL : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      rw [h_P_val, Matrix.map_mul, h_map_U, h_map_V, Matrix.mul_one]
    have h_P_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := rfl
    have h_map_P : (↑P_GL : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      rw [h_P_val, Matrix.map_mul, h_map_U, h_map_V, Matrix.mul_one]
    have h_g1_P : (↑g1 : Matrix (Fin 3) (Fin 3) R) * (↑P_GL : Matrix (Fin 3) (Fin 3) R) = 1 := by
      change (↑(P_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) * (↑P_GL : Matrix (Fin 3) (Fin 3) R) = 1
      exact Units.inv_mul P_GL
    have h_map_g1_P : ((↑g1 : Matrix (Fin 3) (Fin 3) R) * (↑P_GL : Matrix (Fin 3) (Fin 3) R)).map π
    = (1 : Matrix (Fin 3) (Fin 3) R).map π := by
      rw [h_g1_P]
    rw [Matrix.map_mul, h_map_P, Matrix.mul_one, h_map_one] at h_map_g1_P
    have h_final := congr_fun (congr_fun h_map_g1_P i) j
    simp only [Matrix.map_apply, Matrix.one_apply] at h_final
    change π ((↑g1 : Matrix (Fin 3) (Fin 3) R) i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j)
    rw [h_final]
    simp only [Matrix.one_apply]
    split_ifs
    · exact (map_one π).symm
    · exact (map_zero π).symm
  have hd1_goal : innerAutSL3byGL3 R g1 (φ (FieldAutomorpisms.d1SL R)) = FieldAutomorpisms.d1SL R
  := by
    apply Subtype.ext
    change (↑g1 : Matrix (Fin 3) (Fin 3) R) * τ1 * (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = d1m
    have hg1_val : (↑g1 : Matrix (Fin 3) (Fin 3) R) = ↑(P_GL⁻¹) := rfl
    have hg1_inv : (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = ↑P_GL := rfl
    rw [hg1_val, hg1_inv]
    have hP_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := rfl
    have hP_inv : (↑(P_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) = (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) *
    U_inv
    := rfl
    rw [hP_val, hP_inv]
    simp only [Matrix.mul_assoc]
    have h_t1_Uval : τ1 * U_val = U_val * d1m := ht1U_eq_Ud1
    rw [← Matrix.mul_assoc τ1 U_val V]
    rw [h_t1_Uval]
    rw [Matrix.mul_assoc U_val d1m V]
    rw [← Matrix.mul_assoc U_inv U_val (d1m * V)]
    have h_inv_val : U_inv * U_val = 1 := Units.inv_mul U_GL
    rw [h_inv_val]
    rw [Matrix.one_mul]
    rw [hd1_V_comm]
    rw [← Matrix.mul_assoc (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) V d1m]
    have hV_inv_val : (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) * V = 1 := by
      have hV_eq : V = (↑V_GL : Matrix (Fin 3) (Fin 3) R) := rfl
      rw [hV_eq]
      exact Units.inv_mul V_GL
    rw [hV_inv_val]
    rw [Matrix.one_mul]
  have hd2_goal : innerAutSL3byGL3 R g1 (φ (FieldAutomorpisms.d2SL R)) = FieldAutomorpisms.d2SL R
  := by
    apply Subtype.ext
    change (↑g1 : Matrix (Fin 3) (Fin 3) R) * τ2 * (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = d2m
    have hg1_val : (↑g1 : Matrix (Fin 3) (Fin 3) R) = ↑(P_GL⁻¹) := rfl
    have hg1_inv : (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = ↑P_GL := rfl
    rw [hg1_val, hg1_inv]
    have hP_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := rfl
    have hP_inv : (↑(P_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) = (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) *
     U_inv := rfl
    rw [hP_val, hP_inv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc τ2 U_val V]
    rw [← Matrix.mul_assoc U_inv (τ2 * U_val) V]
    rw [← Matrix.mul_assoc U_inv τ2 U_val]
    have h_t2_prime_eq : (U_inv * τ2) * U_val = τ2_prime := rfl
    rw [h_t2_prime_eq]
    have h_t2prime_V : τ2_prime * V = V * d2m := ht2primeV_eq_Vd2
    rw [h_t2prime_V]
    rw [← Matrix.mul_assoc (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) V d2m]
    have hV_inv_val : (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) * V = 1 := by
      have hV_eq : V = (↑V_GL : Matrix (Fin 3) (Fin 3) R) := rfl
      rw [hV_eq]
      exact Units.inv_mul V_GL
    rw [hV_inv_val]
    rw [Matrix.one_mul]
  -- Final Witness & Goal Resolution
  use g1
  refine ⟨hg1_mod_J, hd1_goal, hd2_goal, ?_⟩
  · have hd3_split : FieldAutomorpisms.d3SL R = FieldAutomorpisms.d1SL R * FieldAutomorpisms.d2SL R
     := by
      apply Subtype.ext
      change FieldAutomorpisms.d3 R = FieldAutomorpisms.d1 R * FieldAutomorpisms.d2 R
      dsimp [FieldAutomorpisms.d1, FieldAutomorpisms.d2, FieldAutomorpisms.d3]
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.diagonal_apply_eq]
        fin_cases i <;> simp
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [hd3_split]
    rw [map_mul φ]
    rw [map_mul (innerAutSL3byGL3 R g1)]
    rw [hd1_goal, hd2_goal]

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
  let v1_mat : Matrix (Fin 3) (Fin 3) R := ↑(φ (FieldAutomorpisms.w1SL R))
  let v2_mat : Matrix (Fin 3) (Fin 3) R := ↑(φ (FieldAutomorpisms.w2SL R))
  let π := IsLocalRing.residue R
  -- Extract λ = - v1_mat 0 1 and show it maps to 1 in the residue field.
  have h_map_lam : π (- v1_mat 0 1) = 1 := by
    have hq : π (v1_mat 0 1) = π ((FieldAutomorpisms.w1 R) 0 1) :=
      (Ideal.Quotient.eq (I := J R) (x := v1_mat 0 1) (y := (FieldAutomorpisms.w1 R) 0 1)).mpr
      (hw_mod.1 0 1)
    have hw1_01 : (FieldAutomorpisms.w1 R) 0 1 = -1 := rfl
    rw [hw1_01] at hq
    rw [map_neg, hq, map_neg, map_one, neg_neg]
  have h_lam_unit_pi : IsUnit (π (- v1_mat 0 1)) := by
    rw [h_map_lam]
    exact isUnit_one
  have h_lam_unit : IsUnit (- v1_mat 0 1) := isUnit_of_map_unit π (- v1_mat 0 1) h_lam_unit_pi
  let lam_u : Rˣ := h_lam_unit.unit
  -- Extract μ = v2_mat 1 2 and show it maps to 1 in the residue field.
  have h_map_mu : π (v2_mat 1 2) = 1 := by
    have hq : π (v2_mat 1 2) = π ((FieldAutomorpisms.w2 R) 1 2) :=
      (Ideal.Quotient.eq (I := J R) (x := v2_mat 1 2) (y := (FieldAutomorpisms.w2 R) 1 2)).mpr 
      (hw_mod.2 1 2)
    have hw2_12 : (FieldAutomorpisms.w2 R) 1 2 = 1 := rfl
    rw [hw2_12] at hq
    rw [hq, map_one]
  have h_mu_unit_pi : IsUnit (π (v2_mat 1 2)) := by
    rw [h_map_mu]
    exact isUnit_one
  have h_mu_unit : IsUnit (v2_mat 1 2) := isUnit_of_map_unit π (v2_mat 1 2) h_mu_unit_pi
  let mu_u : Rˣ := h_mu_unit.unit
  -- Define g2 = diag(λ⁻¹, 1, μ)
  let g2_mat : Matrix (Fin 3) (Fin 3) R := Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u]
  have h_g2_det : g2_mat.det = ↑(lam_u⁻¹) * 1 * ↑mu_u := by
    dsimp [g2_mat]
    simp [Matrix.det_diagonal, Fin.prod_univ_three]
  have h_g2_isUnit : IsUnit g2_mat.det := by
    rw [h_g2_det]
    apply IsUnit.mul
    · apply IsUnit.mul
      · exact Units.isUnit lam_u⁻¹
      · exact isUnit_one
    · exact Units.isUnit mu_u
  let g2 : GL3 R := Matrix.nonsingInvUnit g2_mat h_g2_isUnit
  -- Prove g2 ≡ I (mod J)
  have hg2_mod_J : GL3IsOneModJ R g2 := by
    intro i j
    have h_quot := Ideal.Quotient.eq (I := J R) (x := (↑g2 : Matrix (Fin 3) (Fin 3) R) i j) (y := 
    (1 : Matrix (Fin 3) (Fin 3) R) i j)
    apply h_quot.mp
    have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] := rfl
    rw [hg2_val]
    simp only [Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      fin_cases i
      · change π ↑(lam_u⁻¹) = 1
        have h_lam_pi : π (↑lam_u : R) = 1 := h_map_lam
        have h_lam_inv_pi : π (↑(lam_u⁻¹) : R) = 1 := by
          have h_mul : π (↑(lam_u⁻¹) : R) * π (↑lam_u : R) = 1 := by
            rw [← map_mul π, ← Units.val_mul]
            simp
          rw [h_lam_pi, mul_one] at h_mul
          exact h_mul
        exact h_lam_inv_pi
      · change π 1 = 1
        exact map_one π
      · change π (↑mu_u : R) = 1
        exact h_map_mu
    · simp [Matrix.diagonal_apply_ne _ h, map_zero]
      exact h
  -- Prove fixing of d1
  have hd1_goal : innerAutSL3byGL3 R g2 (φ (FieldAutomorpisms.d1SL R)) = FieldAutomorpisms.d1SL R 
  := by
    apply Subtype.ext
    let d1m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d1SL R)
    let τ1 : Matrix (Fin 3) (Fin 3) R := ↑(φ (FieldAutomorpisms.d1SL R))
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * τ1 * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = d1m
    have h_phi_d1 : τ1 = d1m := congrArg Subtype.val hdiag_exact.1
    rw [h_phi_d1]
    have h_comm : (↑g2 : Matrix (Fin 3) (Fin 3) R) * d1m = d1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
    := by
      have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] 
      := rfl
      have hd1_val : d1m = Matrix.diagonal ![1, -1, -1] := rfl
      rw [hg2_val, hd1_val]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [h_comm, Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
  -- Prove fixing of d2
  have hd2_goal : innerAutSL3byGL3 R g2 (φ (FieldAutomorpisms.d2SL R)) = FieldAutomorpisms.d2SL R 
  := by
    apply Subtype.ext
    let d2m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d2SL R)
    let τ2 : Matrix (Fin 3) (Fin 3) R := ↑(φ (FieldAutomorpisms.d2SL R))
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * τ2 * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = d2m
    have h_phi_d2 : τ2 = d2m := congrArg Subtype.val hdiag_exact.2.1
    rw [h_phi_d2]
    have h_comm : (↑g2 : Matrix (Fin 3) (Fin 3) R) * d2m = d2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
    := by
      have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] 
      := rfl
      have hd2_val : d2m = Matrix.diagonal ![-1, 1, -1] := rfl
      rw [hg2_val, hd2_val]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [h_comm, Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
  -- Prove fixing of d3
  have hd3_goal : innerAutSL3byGL3 R g2 (φ (FieldAutomorpisms.d3SL R)) = FieldAutomorpisms.d3SL R 
  := by
    apply Subtype.ext
    let d3m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d3SL R)
    let τ3 : Matrix (Fin 3) (Fin 3) R := ↑(φ (FieldAutomorpisms.d3SL R))
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * τ3 * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = d3m
    have h_phi_d3 : τ3 = d3m := congrArg Subtype.val hdiag_exact.2.2
    rw [h_phi_d3]
    have h_comm : (↑g2 : Matrix (Fin 3) (Fin 3) R) * d3m = d3m * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
    := by
      have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] 
      := rfl
      have hd3_val : d3m = Matrix.diagonal ![-1, -1, 1] := rfl
      rw [hg2_val, hd3_val]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [h_comm, Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
  -- Prove fixing of w1
  have hw1_goal : innerAutSL3byGL3 R g2 (φ (FieldAutomorpisms.w1SL R)) = FieldAutomorpisms.w1SL R 
  := by
    apply Subtype.ext
    let w1m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.w1SL R)
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = w1m
    have h_mul_inv : (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat *
    (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) =
    w1m ↔ (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat = w1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by
      constructor
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat = (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat *
         (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
         := by rw [Matrix.mul_assoc, Units.inv_mul g2, Matrix.mul_one]
             _ = w1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by rw [h]
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) =
        w1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) := by rw [h]
             _ = w1m := by rw [Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
    apply h_mul_inv.mpr
    have h_zero_of_eq_neg (x : R) (h : x = -x) : x = 0 := by
      have h_two : ⅟(2 : R) * 2 = 1 := invOf_mul_self (2 : R)
      have h2 : x * 2 = 0 := by
        calc x * 2 = x - (-x) := by ring
             _ = x - x := by rw [← h]
             _ = 0 := by ring
      calc x = x * 1 := by ring
           _ = x * (⅟(2 : R) * 2) := by rw [← h_two]
           _ = (x * 2) * ⅟(2 : R) := by ring
           _ = 0 * ⅟(2 : R) := by rw [h2]
           _ = 0 := by ring
    let d1m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d1SL R)
    let d2m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d2SL R)
    let d3m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d3SL R)
    have eq_d3 : v1_mat * d3m = d3m * v1_mat := by
      have h_sl3 : FieldAutomorpisms.w1SL R * FieldAutomorpisms.d3SL R =
      FieldAutomorpisms.d3SL R * FieldAutomorpisms.w1SL R := by
        apply Subtype.ext
        change FieldAutomorpisms.w1 R * FieldAutomorpisms.d3 R =
        FieldAutomorpisms.d3 R * FieldAutomorpisms.w1 R
        ext i j
        dsimp [FieldAutomorpisms.w1, FieldAutomorpisms.d3]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v1_mat * (↑(φ (FieldAutomorpisms.d3SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (FieldAutomorpisms.d3SL R)) : Matrix (Fin 3) (Fin 3) R) * v1_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d3 : ↑(φ (FieldAutomorpisms.d3SL R)) = d3m := congrArg Subtype.val hdiag_exact.2.2
      rw [h_phi_d3] at h_mat_eq
      exact h_mat_eq
    have eq_d1 : v1_mat * d1m = d2m * v1_mat := by
      have h_sl3 : FieldAutomorpisms.w1SL R * FieldAutomorpisms.d1SL R =
      FieldAutomorpisms.d2SL R * FieldAutomorpisms.w1SL R := by
        apply Subtype.ext
        change FieldAutomorpisms.w1 R * FieldAutomorpisms.d1 R =
        FieldAutomorpisms.d2 R * FieldAutomorpisms.w1 R
        ext i j
        dsimp [FieldAutomorpisms.w1, FieldAutomorpisms.d1, FieldAutomorpisms.d2]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v1_mat * (↑(φ (FieldAutomorpisms.d1SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (FieldAutomorpisms.d2SL R)) : Matrix (Fin 3) (Fin 3) R) * v1_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d1 : ↑(φ (FieldAutomorpisms.d1SL R)) = d1m := congrArg Subtype.val hdiag_exact.1
      have h_phi_d2 : ↑(φ (FieldAutomorpisms.d2SL R)) = d2m := congrArg Subtype.val hdiag_exact.2.1
      rw [h_phi_d1, h_phi_d2] at h_mat_eq
      exact h_mat_eq
    have eq_sq : v1_mat * v1_mat = d3m := by
      have h_sl3 : FieldAutomorpisms.w1SL R * FieldAutomorpisms.w1SL R =
      FieldAutomorpisms.d3SL R := by
        apply Subtype.ext
        change FieldAutomorpisms.w1 R * FieldAutomorpisms.w1 R = FieldAutomorpisms.d3 R
        ext i j
        dsimp [FieldAutomorpisms.w1, FieldAutomorpisms.d3]
        rw [Matrix.mul_apply]
        rw [Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul] at h_phi_eq
      have h_mat_eq : v1_mat * v1_mat =
      (↑(φ (FieldAutomorpisms.d3SL R)) : Matrix (Fin 3) (Fin 3) R) :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d3 : ↑(φ (FieldAutomorpisms.d3SL R)) = d3m := congrArg Subtype.val hdiag_exact.2.2
      rw [h_phi_d3] at h_mat_eq
      exact h_mat_eq
    have hd3_val : d3m = Matrix.diagonal ![-1, -1, 1] := rfl
    have hd1_val : d1m = Matrix.diagonal ![1, -1, -1] := rfl
    have hd2_val : d2m = Matrix.diagonal ![-1, 1, -1] := rfl
    have hv20 : v1_mat 2 0 = 0 := by
      have h := congr_fun (congr_fun eq_d3 2) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h00 : d3m 0 0 = -1 := rfl
      have h10 : d3m 1 0 = 0 := rfl
      have h20 : d3m 2 0 = 0 := rfl
      have h21 : d3m 2 1 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      rw [h00, h10, h20, h21, h22] at h
      have eq' : v1_mat 2 0 = - (v1_mat 2 0) := by
        calc v1_mat 2 0 = 0 * v1_mat 0 0 + 0 * v1_mat 1 0 + 1 * v1_mat 2 0 := by ring
             _ = v1_mat 2 0 * -1 + v1_mat 2 1 * 0 + v1_mat 2 2 * 0 := h.symm
             _ = - (v1_mat 2 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv21 : v1_mat 2 1 = 0 := by
      have h := congr_fun (congr_fun eq_d3 2) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h01 : d3m 0 1 = 0 := rfl
      have h11 : d3m 1 1 = -1 := rfl
      have h21 : d3m 2 1 = 0 := rfl
      have h20 : d3m 2 0 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      rw [h01, h11, h21, h20, h22] at h
      have eq' : v1_mat 2 1 = - (v1_mat 2 1) := by
        calc v1_mat 2 1 = 0 * v1_mat 0 1 + 0 * v1_mat 1 1 + 1 * v1_mat 2 1 := by ring
             _ = v1_mat 2 0 * 0 + v1_mat 2 1 * -1 + v1_mat 2 2 * 0 := h.symm
             _ = - (v1_mat 2 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv02 : v1_mat 0 2 = 0 := by
      have h := congr_fun (congr_fun eq_d3 0) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02 : d3m 0 2 = 0 := rfl
      have h12 : d3m 1 2 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      have h00 : d3m 0 0 = -1 := rfl
      have h01 : d3m 0 1 = 0 := rfl
      rw [h02, h12, h22, h00, h01] at h
      have eq' : v1_mat 0 2 = - (v1_mat 0 2) := by
        calc v1_mat 0 2 = v1_mat 0 2 * 1 := by ring
             _ = v1_mat 0 0 * 0 + v1_mat 0 1 * 0 + v1_mat 0 2 * 1 := by ring
             _ = -1 * v1_mat 0 2 + 0 * v1_mat 1 2 + 0 * v1_mat 2 2 := h
             _ = - (v1_mat 0 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv12 : v1_mat 1 2 = 0 := by
      have h := congr_fun (congr_fun eq_d3 1) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02 : d3m 0 2 = 0 := rfl
      have h12 : d3m 1 2 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      have h10 : d3m 1 0 = 0 := rfl
      have h11 : d3m 1 1 = -1 := rfl
      rw [h02, h12, h22, h10, h11] at h
      have eq' : v1_mat 1 2 = - (v1_mat 1 2) := by
        calc v1_mat 1 2 = v1_mat 1 0 * 0 + v1_mat 1 1 * 0 + v1_mat 1 2 * 1 := by ring
             _ = 0 * v1_mat 0 2 + -1 * v1_mat 1 2 + 0 * v1_mat 2 2 := h
             _ = - (v1_mat 1 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv00 : v1_mat 0 0 = 0 := by
      have h := congr_fun (congr_fun eq_d1 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd1_00 : d1m 0 0 = 1 := rfl
      have hd1_10 : d1m 1 0 = 0 := rfl
      have hd1_20 : d1m 2 0 = 0 := rfl
      have hd2_00 : d2m 0 0 = -1 := rfl
      have hd2_01 : d2m 0 1 = 0 := rfl
      have hd2_02 : d2m 0 2 = 0 := rfl
      rw [hd1_00, hd1_10, hd1_20, hd2_00, hd2_01, hd2_02] at h
      have eq' : v1_mat 0 0 = - (v1_mat 0 0) := by
        calc v1_mat 0 0 = v1_mat 0 0 * 1 + v1_mat 0 1 * 0 + v1_mat 0 2 * 0 := by ring
             _ = -1 * v1_mat 0 0 + 0 * v1_mat 1 0 + 0 * v1_mat 2 0 := h
             _ = - (v1_mat 0 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv11 : v1_mat 1 1 = 0 := by
      have h := congr_fun (congr_fun eq_d1 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd1_01 : d1m 0 1 = 0 := rfl
      have hd1_11 : d1m 1 1 = -1 := rfl
      have hd1_21 : d1m 2 1 = 0 := rfl
      have hd2_10 : d2m 1 0 = 0 := rfl
      have hd2_11 : d2m 1 1 = 1 := rfl
      have hd2_12 : d2m 1 2 = 0 := rfl
      rw [hd1_01, hd1_11, hd1_21, hd2_10, hd2_11, hd2_12] at h
      have eq' : v1_mat 1 1 = - (v1_mat 1 1) := by
        calc v1_mat 1 1 = 0 * v1_mat 0 1 + 1 * v1_mat 1 1 + 0 * v1_mat 2 1 := by ring
             _ = v1_mat 1 0 * 0 + v1_mat 1 1 * -1 + v1_mat 1 2 * 0 := h.symm
             _ = - (v1_mat 1 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv01_v10 : v1_mat 0 1 * v1_mat 1 0 = -1 := by
      have h := congr_fun (congr_fun eq_sq 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd3_00 : d3m 0 0 = -1 := rfl
      rw [hd3_00, hv00, hv02] at h
      calc v1_mat 0 1 * v1_mat 1 0 = 0 * 0 + v1_mat 0 1 * v1_mat 1 0 + 0 * v1_mat 2 0 := by ring
           _ = -1 := h
    have h_det : v1_mat.det = 1 := (φ (FieldAutomorpisms.w1SL R)).property
    have h_det_exp : v1_mat.det = - (v1_mat 0 1 * v1_mat 1 0 * v1_mat 2 2) := by
      rw [Matrix.det_fin_three]
      rw [hv00, hv11, hv20, hv21, hv02, hv12]
      ring
    have hv22 : v1_mat 2 2 = 1 := by
      calc v1_mat 2 2 = - (-1 * v1_mat 2 2) := by ring
           _ = - (v1_mat 0 1 * v1_mat 1 0 * v1_mat 2 2) := by rw [hv01_v10]
           _ = v1_mat.det := h_det_exp.symm
           _ = 1 := h_det
    have hv01 : v1_mat 0 1 = - ↑lam_u := by
      have h_lam_val : (↑lam_u : R) = - v1_mat 0 1 := rfl
      calc v1_mat 0 1 = - (- v1_mat 0 1) := by ring
           _ = - ↑lam_u := by rw [← h_lam_val]
    have hv10 : v1_mat 1 0 = ↑(lam_u⁻¹) := by
      have h_inv : (↑lam_u : R) * v1_mat 1 0 = 1 := by
        calc (↑lam_u : R) * v1_mat 1 0 = (- v1_mat 0 1) * v1_mat 1 0 := by rw [hv01]; ring
             _ = - (v1_mat 0 1 * v1_mat 1 0) := by ring
             _ = - (-1) := by rw [hv01_v10]
             _ = 1 := by ring
      have h_lam_inv : (↑(lam_u⁻¹) : R) * ↑lam_u = 1 := by
        rw [← Units.val_mul]
        simp
      calc v1_mat 1 0 = 1 * v1_mat 1 0 := by ring
           _ = (↑(lam_u⁻¹) * ↑lam_u) * v1_mat 1 0 := by rw [h_lam_inv]
           _ = ↑(lam_u⁻¹) * ((↑lam_u : R) * v1_mat 1 0) := by ring
           _ = ↑(lam_u⁻¹) * 1 := by rw [h_inv]
           _ = ↑(lam_u⁻¹) := by ring
    ext i j
    have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] := rfl
    rw [hg2_val]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    have h_inv : (↑(lam_u⁻¹) : R) * ↑lam_u = 1 := by
      rw [← Units.val_mul]
      simp
    fin_cases i <;> fin_cases j
    · change (↑(lam_u⁻¹) : R) * v1_mat 0 0 + 0 * v1_mat 1 0 + 0 * v1_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + (-1 : R) * 0 + 0 * 0
      rw [hv00]; ring
    · change (↑(lam_u⁻¹) : R) * v1_mat 0 1 + 0 * v1_mat 1 1 + 0 * v1_mat 2 1 =
      (0 : R) * 0 + (-1 : R) * 1 + 0 * 0
      rw [hv01]
      calc (↑(lam_u⁻¹) : R) * -↑lam_u + 0 * v1_mat 1 1 + 0 * v1_mat 2 1
        _ = -((↑(lam_u⁻¹) : R) * ↑lam_u) := by ring
        _ = -1 := by rw [h_inv]
        _ = (0 : R) * 0 + (-1 : R) * 1 + 0 * 0 := by ring
    · change (↑(lam_u⁻¹) : R) * v1_mat 0 2 + 0 * v1_mat 1 2 + 0 * v1_mat 2 2 =
      (0 : R) * 0 + (-1 : R) * 0 + 0 * ↑mu_u
      rw [hv02]; ring
    · change (0 : R) * v1_mat 0 0 + 1 * v1_mat 1 0 + 0 * v1_mat 2 0 =
      (1 : R) * ↑(lam_u⁻¹) + 0 * 0 + 0 * 0
      rw [hv10]; ring
    · change (0 : R) * v1_mat 0 1 + 1 * v1_mat 1 1 + 0 * v1_mat 2 1 =
      (1 : R) * 0 + 0 * 1 + 0 * 0
      rw [hv11]; ring
    · change (0 : R) * v1_mat 0 2 + 1 * v1_mat 1 2 + 0 * v1_mat 2 2 =
      (1 : R) * 0 + 0 * 0 + 0 * ↑mu_u
      rw [hv12]; ring
    · change (0 : R) * v1_mat 0 0 + 0 * v1_mat 1 0 + ↑mu_u * v1_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + 0 * 0 + 1 * 0
      rw [hv20]; ring
    · change (0 : R) * v1_mat 0 1 + 0 * v1_mat 1 1 + ↑mu_u * v1_mat 2 1 =
      (0 : R) * 0 + 0 * 1 + 1 * 0
      rw [hv21]; ring
    · change (0 : R) * v1_mat 0 2 + 0 * v1_mat 1 2 + ↑mu_u * v1_mat 2 2 =
      (0 : R) * 0 + 0 * 0 + 1 * ↑mu_u
      rw [hv22]; ring
  -- Prove fixing of w2
  have hw2_goal : innerAutSL3byGL3 R g2 (φ (FieldAutomorpisms.w2SL R)) =
  FieldAutomorpisms.w2SL R := by
    apply Subtype.ext
    let w2m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.w2SL R)
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = w2m
    have h_mul_inv : (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat *
    (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = w2m ↔ (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat =
    w2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by
      constructor
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat = (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat *
        (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) * (↑g2 : Matrix (Fin 3) (Fin 3) R)
        := by rw [Matrix.mul_assoc, Units.inv_mul g2, Matrix.mul_one]
             _ = w2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by rw [h]
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) =
        w2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) := by rw [h]
             _ = w2m := by rw [Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
    apply h_mul_inv.mpr
    have h_zero_of_eq_neg (x : R) (h : x = -x) : x = 0 := by
      have h_two : ⅟(2 : R) * 2 = 1 := invOf_mul_self (2 : R)
      have h2 : x * 2 = 0 := by
        calc x * 2 = x - (-x) := by ring
             _ = x - x := by rw [← h]
             _ = 0 := by ring
      calc x = x * 1 := by ring
           _ = x * (⅟(2 : R) * 2) := by rw [← h_two]
           _ = (x * 2) * ⅟(2 : R) := by ring
           _ = 0 * ⅟(2 : R) := by rw [h2]
           _ = 0 := by ring
    let d1m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d1SL R)
    let d2m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d2SL R)
    let d3m : Matrix (Fin 3) (Fin 3) R := ↑(FieldAutomorpisms.d3SL R)
    have eq_d1_v2 : v2_mat * d1m = d1m * v2_mat := by
      have h_sl3 : FieldAutomorpisms.w2SL R * FieldAutomorpisms.d1SL R =
      FieldAutomorpisms.d1SL R * FieldAutomorpisms.w2SL R := by
        apply Subtype.ext
        change FieldAutomorpisms.w2 R * FieldAutomorpisms.d1 R =
        FieldAutomorpisms.d1 R * FieldAutomorpisms.w2 R
        ext i j
        dsimp [FieldAutomorpisms.w2, FieldAutomorpisms.d1]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v2_mat * (↑(φ (FieldAutomorpisms.d1SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (FieldAutomorpisms.d1SL R)) : Matrix (Fin 3) (Fin 3) R) * v2_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d1 : ↑(φ (FieldAutomorpisms.d1SL R)) = d1m := congrArg Subtype.val hdiag_exact.1
      rw [h_phi_d1] at h_mat_eq
      exact h_mat_eq
    have eq_d2_v2 : v2_mat * d2m = d3m * v2_mat := by
      have h_sl3 : FieldAutomorpisms.w2SL R * FieldAutomorpisms.d2SL R =
      FieldAutomorpisms.d3SL R * FieldAutomorpisms.w2SL R := by
        apply Subtype.ext
        change FieldAutomorpisms.w2 R * FieldAutomorpisms.d2 R =
        FieldAutomorpisms.d3 R * FieldAutomorpisms.w2 R
        ext i j
        dsimp [FieldAutomorpisms.w2, FieldAutomorpisms.d2, FieldAutomorpisms.d3]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v2_mat * (↑(φ (FieldAutomorpisms.d2SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (FieldAutomorpisms.d3SL R)) : Matrix (Fin 3) (Fin 3) R) * v2_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d2 : ↑(φ (FieldAutomorpisms.d2SL R)) = d2m := congrArg Subtype.val hdiag_exact.2.1
      have h_phi_d3 : ↑(φ (FieldAutomorpisms.d3SL R)) = d3m := congrArg Subtype.val hdiag_exact.2.2
      rw [h_phi_d2, h_phi_d3] at h_mat_eq
      exact h_mat_eq
    have eq_sq_v2 : v2_mat * v2_mat = d1m := by
      have h_sl3 : FieldAutomorpisms.w2SL R * FieldAutomorpisms.w2SL R =
      FieldAutomorpisms.d1SL R := by
        apply Subtype.ext
        change FieldAutomorpisms.w2 R * FieldAutomorpisms.w2 R = FieldAutomorpisms.d1 R
        ext i j
        dsimp [FieldAutomorpisms.w2, FieldAutomorpisms.d1]
        rw [Matrix.mul_apply]
        rw [Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul] at h_phi_eq
      have h_mat_eq : v2_mat * v2_mat =
      (↑(φ (FieldAutomorpisms.d1SL R)) : Matrix (Fin 3) (Fin 3) R) :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d1 : ↑(φ (FieldAutomorpisms.d1SL R)) = d1m := congrArg Subtype.val hdiag_exact.1
      rw [h_phi_d1] at h_mat_eq
      exact h_mat_eq
    have hd1_val : d1m = Matrix.diagonal ![1, -1, -1] := rfl
    have hd2_val : d2m = Matrix.diagonal ![-1, 1, -1] := rfl
    have hd3_val : d3m = Matrix.diagonal ![-1, -1, 1] := rfl
    have hv01 : v2_mat 0 1 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 0) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h01_1 : d1m 0 1 = 0 := rfl
      have h11_1 : d1m 1 1 = -1 := rfl
      have h21_1 : d1m 2 1 = 0 := rfl
      have h00_1 : d1m 0 0 = 1 := rfl
      have h02_1 : d1m 0 2 = 0 := rfl
      rw [h01_1, h11_1, h21_1, h00_1, h02_1] at h
      have eq' : v2_mat 0 1 = - (v2_mat 0 1) := by
        calc v2_mat 0 1 = 1 * v2_mat 0 1 + 0 * v2_mat 1 1 + 0 * v2_mat 2 1 := by ring
             _ = v2_mat 0 0 * 0 + v2_mat 0 1 * -1 + v2_mat 0 2 * 0 := h.symm
             _ = - (v2_mat 0 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv02 : v2_mat 0 2 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 0) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02_1 : d1m 0 2 = 0 := rfl
      have h12_1 : d1m 1 2 = 0 := rfl
      have h22_1 : d1m 2 2 = -1 := rfl
      have h00_1 : d1m 0 0 = 1 := rfl
      have h01_1 : d1m 0 1 = 0 := rfl
      rw [h02_1, h12_1, h22_1, h00_1, h01_1] at h
      have eq' : v2_mat 0 2 = - (v2_mat 0 2) := by
        calc v2_mat 0 2 = 1 * v2_mat 0 2 + 0 * v2_mat 1 2 + 0 * v2_mat 2 2 := by ring
             _ = v2_mat 0 0 * 0 + v2_mat 0 1 * 0 + v2_mat 0 2 * -1 := h.symm
             _ = - (v2_mat 0 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv10 : v2_mat 1 0 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 1) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h00_1 : d1m 0 0 = 1 := rfl
      have h10_1 : d1m 1 0 = 0 := rfl
      have h20_1 : d1m 2 0 = 0 := rfl
      have h11_1 : d1m 1 1 = -1 := rfl
      have h12_1 : d1m 1 2 = 0 := rfl
      rw [h00_1, h10_1, h20_1, h11_1, h12_1] at h
      have eq' : v2_mat 1 0 = - (v2_mat 1 0) := by
        calc v2_mat 1 0 = v2_mat 1 0 * 1 + v2_mat 1 1 * 0 + v2_mat 1 2 * 0 := by ring
             _ = 0 * v2_mat 0 0 + -1 * v2_mat 1 0 + 0 * v2_mat 2 0 := h
             _ = - (v2_mat 1 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv20 : v2_mat 2 0 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 2) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h00_1 : d1m 0 0 = 1 := rfl
      have h10_1 : d1m 1 0 = 0 := rfl
      have h20_1 : d1m 2 0 = 0 := rfl
      have h21_1 : d1m 2 1 = 0 := rfl
      have h22_1 : d1m 2 2 = -1 := rfl
      rw [h00_1, h10_1, h20_1, h21_1, h22_1] at h
      have eq' : v2_mat 2 0 = - (v2_mat 2 0) := by
        calc v2_mat 2 0 = v2_mat 2 0 * 1 + v2_mat 2 1 * 0 + v2_mat 2 2 * 0 := by ring
             _ = 0 * v2_mat 0 0 + 0 * v2_mat 1 0 + -1 * v2_mat 2 0 := h
             _ = - (v2_mat 2 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv11 : v2_mat 1 1 = 0 := by
      have h := congr_fun (congr_fun eq_d2_v2 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h01_2 : d2m 0 1 = 0 := rfl
      have h11_2 : d2m 1 1 = 1 := rfl
      have h21_2 : d2m 2 1 = 0 := rfl
      have h10_3 : d3m 1 0 = 0 := rfl
      have h11_3 : d3m 1 1 = -1 := rfl
      have h12_3 : d3m 1 2 = 0 := rfl
      rw [h01_2, h11_2, h21_2, h10_3, h11_3, h12_3] at h
      have eq' : v2_mat 1 1 = - (v2_mat 1 1) := by
        calc v2_mat 1 1 = v2_mat 1 0 * 0 + v2_mat 1 1 * 1 + v2_mat 1 2 * 0 := by ring
             _ = 0 * v2_mat 0 1 + -1 * v2_mat 1 1 + 0 * v2_mat 2 1 := h
             _ = - (v2_mat 1 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv22 : v2_mat 2 2 = 0 := by
      have h := congr_fun (congr_fun eq_d2_v2 2) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02_2 : d2m 0 2 = 0 := rfl
      have h12_2 : d2m 1 2 = 0 := rfl
      have h22_2 : d2m 2 2 = -1 := rfl
      have h20_3 : d3m 2 0 = 0 := rfl
      have h21_3 : d3m 2 1 = 0 := rfl
      have h22_3 : d3m 2 2 = 1 := rfl
      rw [h02_2, h12_2, h22_2, h20_3, h21_3, h22_3] at h
      have eq' : v2_mat 2 2 = - (v2_mat 2 2) := by
        calc v2_mat 2 2 = 0 * v2_mat 0 2 + 0 * v2_mat 1 2 + 1 * v2_mat 2 2 := by ring
             _ = v2_mat 2 0 * 0 + v2_mat 2 1 * 0 + v2_mat 2 2 * -1 := h.symm
             _ = - (v2_mat 2 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv12_v21 : v2_mat 1 2 * v2_mat 2 1 = -1 := by
      have h := congr_fun (congr_fun eq_sq_v2 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd1_11 : d1m 1 1 = -1 := rfl
      rw [hd1_11, hv10, hv11] at h
      calc v2_mat 1 2 * v2_mat 2 1 = 0 * v2_mat 0 1 + 0 * 0 + v2_mat 1 2 * v2_mat 2 1 := by ring
           _ = -1 := h
    have h_det : v2_mat.det = 1 := (φ (FieldAutomorpisms.w2SL R)).property
    have h_det_exp : v2_mat.det = - (v2_mat 0 0 * v2_mat 1 2 * v2_mat 2 1) := by
      rw [Matrix.det_fin_three]
      rw [hv01, hv02, hv10, hv20, hv11, hv22]
      ring
    have hv00 : v2_mat 0 0 = 1 := by
      calc v2_mat 0 0 = - (-1 * v2_mat 0 0) := by ring
           _ = - (v2_mat 1 2 * v2_mat 2 1 * v2_mat 0 0) := by rw [hv12_v21]
           _ = - (v2_mat 0 0 * v2_mat 1 2 * v2_mat 2 1) := by ring
           _ = v2_mat.det := h_det_exp.symm
           _ = 1 := h_det
    have hv12 : v2_mat 1 2 = ↑mu_u := by
      have h_mu_val : (↑mu_u : R) = v2_mat 1 2 := rfl
      rw [← h_mu_val]
    have hv21 : v2_mat 2 1 = - ↑(mu_u⁻¹) := by
      have h_inv : (↑mu_u : R) * (- v2_mat 2 1) = 1 := by
        calc (↑mu_u : R) * (- v2_mat 2 1) = - (v2_mat 1 2 * v2_mat 2 1) := by rw [hv12]; ring
             _ = - (-1) := by rw [hv12_v21]
             _ = 1 := by ring
      have h_mu_inv : (↑(mu_u⁻¹) : R) * ↑mu_u = 1 := by
        rw [← Units.val_mul]
        simp
      have h_neg_v21 : - v2_mat 2 1 = ↑(mu_u⁻¹) := by
        calc - v2_mat 2 1 = 1 * (- v2_mat 2 1) := by ring
             _ = (↑(mu_u⁻¹) * ↑mu_u) * (- v2_mat 2 1) := by rw [h_mu_inv]
             _ = ↑(mu_u⁻¹) * ((↑mu_u : R) * (- v2_mat 2 1)) := by ring
             _ = ↑(mu_u⁻¹) * 1 := by rw [h_inv]
             _ = ↑(mu_u⁻¹) := by ring
      calc v2_mat 2 1 = - (- v2_mat 2 1) := by ring
           _ = - ↑(mu_u⁻¹) := by rw [h_neg_v21]
    ext i j
    have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] := rfl
    rw [hg2_val]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    have h_inv : ↑mu_u * (↑(mu_u⁻¹) : R) = 1 := by 
      rw [← Units.val_mul]
      simp
    fin_cases i <;> fin_cases j
    · change (↑(lam_u⁻¹) : R) * v2_mat 0 0 + 0 * v2_mat 1 0 + 0 * v2_mat 2 0 =
      (1 : R) * ↑(lam_u⁻¹) + 0 * 0 + 0 * 0
      rw [hv00]; ring
    · change (↑(lam_u⁻¹) : R) * v2_mat 0 1 + 0 * v2_mat 1 1 + 0 * v2_mat 2 1 =
      (1 : R) * 0 + 0 * 1 + 0 * 0
      rw [hv01]; ring
    · change (↑(lam_u⁻¹) : R) * v2_mat 0 2 + 0 * v2_mat 1 2 + 0 * v2_mat 2 2 =
      (1 : R) * 0 + 0 * 0 + 0 * ↑mu_u
      rw [hv02]; ring
    · change (0 : R) * v2_mat 0 0 + 1 * v2_mat 1 0 + 0 * v2_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + 0 * 0 + 1 * 0
      rw [hv10]; ring
    · change (0 : R) * v2_mat 0 1 + 1 * v2_mat 1 1 + 0 * v2_mat 2 1 =
      (0 : R) * 0 + 0 * 1 + 1 * 0
      rw [hv11]; ring
    · change (0 : R) * v2_mat 0 2 + 1 * v2_mat 1 2 + 0 * v2_mat 2 2 =
      (0 : R) * 0 + 0 * 0 + 1 * ↑mu_u
      rw [hv12]; ring
    · change (0 : R) * v2_mat 0 0 + 0 * v2_mat 1 0 + ↑mu_u * v2_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + (-1 : R) * 0 + 0 * 0
      rw [hv20]; ring
    · change (0 : R) * v2_mat 0 1 + 0 * v2_mat 1 1 + ↑mu_u * v2_mat 2 1 =
      (0 : R) * 0 + (-1 : R) * 1 + 0 * 0
      rw [hv21, hv01, hv11]
      calc (0 : R) * 0 + 0 * 0 + ↑mu_u * -↑(mu_u⁻¹)
        _ = -(↑mu_u * ↑(mu_u⁻¹)) := by ring
        _ = -1 := by rw [h_inv]
        _ = (0 : R) * 0 + (-1 : R) * 1 + 0 * 0 := by ring
    · change (0 : R) * v2_mat 0 2 + 0 * v2_mat 1 2 + ↑mu_u * v2_mat 2 2 =
      (0 : R) * 0 + (-1 : R) * 0 + 0 * ↑mu_u
      rw [hv22]; ring
  use g2

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
