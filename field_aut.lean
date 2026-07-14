import Final_Project.cong_subgroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs


open Matrix BigOperators
open scoped MatrixGroups
noncomputable section



abbrev GL3 (A : Type*) [CommRing A] : Type _ :=
  GL (Fin 3) A



variable (R : Type*) [CommRing R] [Invertible (2 : R)]



abbrev AutSL3 : Type _ :=
  SL3 R ≃* SL3 R



def ringAutMapSL3 (σ : R ≃+* R) (x : SL3 R) : SL3 R :=
  ⟨((x : Matrix (Fin 3) (Fin 3) R).map σ), by
    -- Need determinant compatibility with entrywise ring automorphisms.
   calc
      ((x : Matrix (Fin 3) (Fin 3) R).map ⇑σ).det
          = σ ((x : Matrix (Fin 3) (Fin 3) R).det) := by
              simpa only [RingEquiv.mapMatrix_apply] using
                (σ.map_det
                  (x : Matrix (Fin 3) (Fin 3) R)).symm
      _ = 1 := by simp [x.property]⟩


def ringAutSL3 (σ : R ≃+* R) : AutSL3 R where
  toFun := ringAutMapSL3 R σ
  invFun := ringAutMapSL3 R σ.symm

  left_inv := by
    intro x
    apply Subtype.ext
    dsimp [ringAutMapSL3]
    simp
    ext i j
    dsimp [map]
    exact RingEquiv.symm_apply_apply σ _



  right_inv := by
    intro x
    apply Subtype.ext
    dsimp [ringAutMapSL3]
    simp
    ext i j
    dsimp [map]
    exact RingEquiv.symm_apply_apply σ.symm _


  map_mul' := by
    intro x y
    apply Subtype.ext
    ext i j
    simp [ringAutMapSL3, Matrix.mul_apply]



def innerAutSL3byGL3 (g : GL3 R) : MulAut (SL3 R) where
  toFun := fun x => ⟨g * Matrix.SpecialLinearGroup.toGL x * g⁻¹, by
    simp [Matrix.det_mul,  Ring.mul_inverse_cancel]⟩
  invFun := fun x =>⟨g⁻¹ * Matrix.SpecialLinearGroup.toGL x * g, by
    simp [Matrix.det_mul, Ring.inverse_mul_cancel]⟩

  left_inv := by
    intro x
    simp [mul_assoc]

  right_inv := by
    intro x
    simp [mul_assoc]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [mul_assoc]

def invTransposeMap (x : SL3 R) : SL3 R :=
  ⟨(((x⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R).transpose), by
    rw [Matrix.det_transpose]
    exact (x⁻¹ : SL3 R).property⟩


def invTransposeAutSL3 : AutSL3 R where
  toFun := invTransposeMap R
  invFun := invTransposeMap R

  left_inv := by
    intro x
    apply Subtype.ext
    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp
    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  right_inv := by
    intro x
    apply Subtype.ext
    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp

    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [invTransposeMap, Matrix.transpose_mul]





theorem zero_iff_eq_neg_self {R : Type*} [Ring R] [Invertible (2 : R)] (x : R):
  0 = x ↔ x = -x := by
  constructor
  · intro h
    rw [← h, neg_zero]
  · intro h
    rw [← one_mul x, ← invOf_mul_self (2 : R), mul_assoc, two_mul, add_eq_zero_iff_eq_neg.mpr h,
        mul_zero]

namespace FieldAutomorpisms


variable (F : Type*) [Field F] [Invertible (2 : F)]





def d1 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![1, -1, -1]

def d2 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, 1, -1]

def d3 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, -1, 1]

def d1SL : SL3 R :=
  ⟨d1 R, by
    simp [d1, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d2SL : SL3 R :=
  ⟨d2 R, by
    simp [d2, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d3SL : SL3 R :=
  ⟨d3 R, by
    simp [d3, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

theorem diag_preserved_after_change_of_basis
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 F g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 F g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 F g (φ (d3SL F)) = d3SL F := by
  sorry


def w1 : Matrix (Fin 3) (Fin 3) (R) :=
    !![0, 1, 0;
     -1, 0, 0;
     0, 0, 1]

def w2 : Matrix (Fin 3) (Fin 3) (R) :=
    !![1, 0, 0;
     0, 0, 1;
     0, -1, 0]

def w1SL : SL3 R :=
  ⟨w1 R, by
    simp [w1, Matrix.det_fin_three]
  ⟩

def w2SL : SL3 R :=
  ⟨w2 R, by
    simp [w2, Matrix.det_fin_three]
  ⟩

theorem w_preserved
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 F g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 F g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 F g (φ (d3SL F)) = d3SL F ∧
      innerAutSL3byGL3 F g (φ (w1SL F)) = w1SL F ∧
      innerAutSL3byGL3 F g (φ (w2SL F)) = w2SL F := by
  rcases diag_preserved_after_change_of_basis F φ with ⟨g, hd1, hd2, hd3⟩
  let v1 := (innerAutSL3byGL3 F g (φ (w1SL F))).val
  let v2 := (innerAutSL3byGL3 F g (φ (w2SL F))).val
  have hv1: ∃ l : F, IsUnit l ∧ v1 =
    !![0,    l, 0;
       -l⁻¹, 0, 0;
       0,    0, 1] := by
    use v1 0 1
    have first_rep:
          !![v1 0 0, v1 0 1, 0;
             v1 1 0, v1 1 1, 0;
             0,      0,      v1 2 2] = v1 := by
      have (i : Fin 3) (j : Fin 3):
           !![v1 0 0,  v1 0 1,  -v1 0 2;
              v1 1 0,  v1 1 1,  -v1 1 2;
              -v1 2 0, -v1 2 1, v1 2 2] i j = v1 i j := by
        have: (d3 F) * v1 * (d3 F) = v1 := by
          have: (innerAutSL3byGL3 F g (φ ((d3SL F) * (w1SL F) * (d3SL F)))) =
                 innerAutSL3byGL3 F g (φ (w1SL F)) := by
            have: (d3SL F) * (w1SL F) * (d3SL F) = w1SL F := by
              have: (d3 F) * (w1 F) * (d3 F) = w1 F := by
                rw [w1, d3, diagonal_fin_three, mul_fin_three, mul_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd3] at this
          simp only [v1]
          nth_rw 2 [← this]
          exact ext fun i => congrFun rfl
        rw [d3, diagonal_fin_three] at this
        nth_rw 10 [← this, eta_fin_three v1]
        simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact (zero_iff_eq_neg_self _).mpr (this 0 2).symm
      · exact (zero_iff_eq_neg_self _).mpr (this 1 2).symm
      · exact (zero_iff_eq_neg_self _).mpr (this 2 0).symm
      · exact (zero_iff_eq_neg_self _).mpr (this 2 1).symm
    have second_rep:
          !![0,      v1 0 1, 0;
             v1 1 0, 0,      0;
             0,      0,      v1 2 2] = v1 := by
      have: v1 * (d1 F) = (d2 F) * v1 := by
        have: v1 * (d1SL F) = (d2SL F) * v1 := by
          have: (innerAutSL3byGL3 F g (φ ((w1SL F) * (d1SL F)))) =
                innerAutSL3byGL3 F g (φ ((d2SL F) * (w1SL F))) := by
            have: (w1SL F) * (d1SL F) = (d2SL F) * (w1SL F) := by
              have: (w1 F) * (d1 F) = (d2 F) * (w1 F) := by
                rw [w1, d1, d2, diagonal_fin_three, diagonal_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd2, hd1] at this
          rw [← SpecialLinearGroup.coe_mul, this]
          rfl
        exact this
      rw [d1, d2, diagonal_fin_three, diagonal_fin_three, ← first_rep] at this
      simp at this
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact (zero_iff_eq_neg_self _).mpr this.left
      · exact (zero_iff_eq_neg_self _).mpr this.right.symm
    have det_v1: det v1 = 1 := by
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v101: IsUnit (v1 0 1) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, det_fin_three] at det_v1
      simp at det_v1
    have third_rep:
          !![0,           v1 0 1, 0;
             -(v1 0 1)⁻¹, 0,      0;
             0,           0,      1] = v1 := by
      nth_rw 3 [← second_rep]
      have: v1 * v1 = d3 F := by
        have: (innerAutSL3byGL3 F g (φ ((w1SL F) * (w1SL F)))) =
              innerAutSL3byGL3 F g (φ (d3SL F)) := by
          have: (w1SL F) * (w1SL F) = (d3SL F) := by
            have: (w1 F) * (w1 F) = (d3 F) := by
              rw [w1, d3, diagonal_fin_three, mul_fin_three]
              simp
            apply Subtype.ext this
          rw [this]
        rw [map_mul, map_mul, hd3] at this
        simp only [v1]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      rw [← second_rep, d3, diagonal_fin_three] at this
      simp at this
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · rw [neg_eq_neg_one_mul, ← this.right.left, mul_assoc, not_zero_v101.mul_inv_cancel,
            mul_one]
      · have det_calc: 1 = -((v1 0 1) * (v1 1 0)) * (v1 2 2) := by
          nth_rw 1 [← det_v1, ← second_rep]
          rw [det_fin_three]
          simp
        rw [this.left, neg_neg, one_mul] at det_calc
        exact det_calc
    exact ⟨ not_zero_v101, third_rep.symm ⟩
  have hv2: ∃ l : F, IsUnit l ∧ v2 =
    !![1, 0,    0;
       0, 0,    l;
       0, -l⁻¹, 0] := by
    use v2 1 2
    have first_rep:
          !![v2 0 0, 0,      0;
             0,      v2 1 1, v2 1 2;
             0,      v2 2 1, v2 2 2] = v2 := by
      have (i : Fin 3) (j : Fin 3):
           !![v2 0 0,   -v2 0 1,  -v2 0 2;
              -v2 1 0,  v2 1 1,   v2 1 2;
              -v2 2 0,  v2 2 1,   v2 2 2] i j = v2 i j := by
        have: (d1 F) * v2 * (d1 F) = v2 := by
          have: (innerAutSL3byGL3 F g (φ ((d1SL F) * (w2SL F) * (d1SL F)))) =
                 innerAutSL3byGL3 F g (φ (w2SL F)) := by
            have: (d1SL F) * (w2SL F) * (d1SL F) = w2SL F := by
              have: (d1 F) * (w2 F) * (d1 F) = w2 F := by
                rw [w2, d1, diagonal_fin_three, mul_fin_three, mul_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd1] at this
          simp only [v2]
          nth_rw 2 [← this]
          rfl
        rw [d1, diagonal_fin_three] at this
        nth_rw 10 [← this, eta_fin_three v2]
        simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact (zero_iff_eq_neg_self _).mpr (this 0 1).symm
      · exact (zero_iff_eq_neg_self _).mpr (this 0 2).symm
      · exact (zero_iff_eq_neg_self _).mpr (this 1 0).symm
      · exact (zero_iff_eq_neg_self _).mpr (this 2 0).symm
    have second_rep:
          !![v2 0 0, 0,      0;
             0,      0, v2 1 2;
             0,      v2 2 1, 0] = v2 := by
      have: v2 * (d3 F) = (d2 F) * v2 := by
        have: v2 * (d3SL F) = (d2SL F) * v2 := by
          have: (innerAutSL3byGL3 F g (φ ((w2SL F) * (d3SL F)))) =
                innerAutSL3byGL3 F g (φ ((d2SL F) * (w2SL F))) := by
            have: (w2SL F) * (d3SL F) = (d2SL F) * (w2SL F) := by
              have: (w2 F) * (d3 F) = (d2 F) * (w2 F) := by
                rw [w2, d3, d2, diagonal_fin_three, diagonal_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd2, hd3] at this
          rw [← SpecialLinearGroup.coe_mul, this]
          rfl
        exact this
      rw [d3, d2, diagonal_fin_three, diagonal_fin_three, ← first_rep] at this
      simp at this
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact (zero_iff_eq_neg_self _).mpr this.left.symm
      · exact (zero_iff_eq_neg_self _).mpr this.right
    have det_v2: det v2 = 1 := by
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v212: IsUnit (v2 1 2) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, det_fin_three] at det_v2
      simp at det_v2
    have third_rep:
          !![1, 0,           0;
             0, 0,           v2 1 2;
             0, -(v2 1 2)⁻¹, 0] = v2 := by
      nth_rw 3 [← second_rep]
      have: v2 * v2 = d1 F := by
        have: (innerAutSL3byGL3 F g (φ ((w2SL F) * (w2SL F)))) =
              innerAutSL3byGL3 F g (φ (d1SL F)) := by
          have: (w2SL F) * (w2SL F) = (d1SL F) := by
            have: (w2 F) * (w2 F) = (d1 F) := by
              rw [w2, d1, diagonal_fin_three, mul_fin_three]
              simp
            apply Subtype.ext this
          rw [this]
        rw [map_mul, map_mul, hd1] at this
        simp only [v2]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      rw [← second_rep, d1, diagonal_fin_three] at this
      simp at this
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · have det_calc: 1 = - (v2 0 0) * (v2 1 2) * (v2 2 1) := by
          nth_rw 1 [← det_v2, ← second_rep]
          rw [det_fin_three]
          simp
        rw [mul_assoc, this.right.left, neg_mul_neg, mul_one] at det_calc
        exact det_calc
      · rw [neg_eq_neg_one_mul, ← this.right.right, mul_assoc, not_zero_v212.mul_inv_cancel,
            mul_one]
    exact ⟨ not_zero_v212, third_rep.symm ⟩
  rcases hv1 with ⟨l1, l1unit, hl1⟩
  rcases hv2 with ⟨l2, l2unit, hl2⟩
  use ⟨!![l1⁻¹, 0, 0;
          0,   1, 0;
          0,   0, l2] * g,
      g⁻¹ * !![l1, 0, 0;
                0,   1, 0;
                0,   0, l2⁻¹],
      by
        rw [mul_assoc, ← mul_assoc _ _ !![l1, 0, 0; 0, 1, 0; 0, 0, l2⁻¹], g.mul_inv, one_mul,
            mul_fin_three, l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]
        simp only [zero_mul, add_zero, mul_zero, zero_add]
        rw [mul_one, one_fin_three],
      by
        rw [← mul_assoc, mul_assoc _ !![l1, 0, 0; 0, 1, 0; 0, 0, l2⁻¹], mul_fin_three,
            l1unit.mul_inv_cancel, l2unit.inv_mul_cancel]
        simp only [zero_mul, add_zero, mul_zero, zero_add]
        rw [mul_one, ← one_fin_three, mul_one, g.inv_mul]
      ⟩
  simp only [innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk, Units.inv_mk]
  have diag_preserved:
    g * SpecialLinearGroup.toGL (φ (d1SL F)) * g⁻¹ = d1 F ∧
    g * SpecialLinearGroup.toGL (φ (d2SL F)) * g⁻¹ = d2 F ∧
    g * SpecialLinearGroup.toGL (φ (d3SL F)) * g⁻¹ = d3 F :=
      ⟨ congrArg Subtype.val hd1, congrArg Subtype.val hd2, congrArg Subtype.val hd3 ⟩
  exact ⟨
    by
      congr
      rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
          mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], diag_preserved.left, d1, diagonal_fin_three]
      simp
      exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩,
    by
      congr
      rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
          mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], diag_preserved.right.left, d2,
          diagonal_fin_three]
      simp
      exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩,
    by
      congr
      rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
          mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], diag_preserved.right.right, d3,
          diagonal_fin_three]
      simp
      exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩,
    by
      congr
      simp only [v1, innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk] at hl1
      rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
          mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], hl1, w1, mul_fin_three, mul_fin_three]
      simp only [zero_mul, add_zero, mul_zero, zero_add]
      rw [mul_one, mul_one, one_mul, neg_eq_neg_one_mul, mul_assoc, l2unit.mul_inv_cancel,
          l1unit.inv_mul_cancel, mul_one],
    by
      congr
      simp only [v2, innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk] at hl2
      rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
          mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], hl2, w2, mul_fin_three, mul_fin_three]
      simp only [zero_mul, add_zero, mul_zero, zero_add]
      rw [mul_one, mul_one, one_mul, neg_eq_neg_one_mul, ← mul_assoc, mul_comm _ (-1), mul_assoc,
          l2unit.mul_inv_cancel, l1unit.inv_mul_cancel, mul_one]
  ⟩


def x12 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def x12SL : SL3 R :=
  ⟨x12 R, by simp [x12, Matrix.det_fin_three]⟩

def x13 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def x13SL : SL3 R :=
  ⟨x13 R, by simp [x13, Matrix.det_fin_three]⟩

def x23 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def x23SL : SL3 R :=
  ⟨x23 R, by simp [x23, Matrix.det_fin_three]⟩

def graphChoiceSL3 (ε : Bool) : AutSL3 R :=
  if ε then invTransposeAutSL3 R else (1 : AutSL3 R)

/--
# Preservation of Standard Matrices under Contragredient
Proves that the contragredient automorphism `Λ(A) := (A⁻¹)ᵀ` (formally `invTransposeAutSL3`)
preserves the involutions `d₁`, `d₂`, `d₃` and the signed transpositions `w₁`, `w₂`.

## Mathematical Insight
Rather than calculating the explicit adjugate matrices or wrestling with matrix inverses directly,
this proof exploits the orthogonal and symmetric nature of the target matrices. For each of these
specific matrices `A`, we show that `Aᵀ * A = 1`. By the uniqueness of inverses, this implies
`A⁻¹ = Aᵀ`, which means `Λ(A) = (Aᵀ)ᵀ = A`.
-/
theorem invTranspose_preserves_d_w (F : Type*) [Field F] [Invertible (2 : F)] :
    invTransposeAutSL3 F (d1SL F) = d1SL F ∧
    invTransposeAutSL3 F (d2SL F) = d2SL F ∧
    invTransposeAutSL3 F (d3SL F) = d3SL F ∧
    invTransposeAutSL3 F (w1SL F) = w1SL F ∧
    invTransposeAutSL3 F (w2SL F) = w2SL F := by

  -- We prove preservation for d₁ by demonstrating that d₁ᵀ * d₁ = 1.
  have hd1 : invTransposeAutSL3 F (d1SL F) = d1SL F := by
    -- We explicitly construct the transpose of d₁ as an SL₃ element.
    let d1T_SL : SL3 F := ⟨(d1 F).transpose, by rw [Matrix.det_transpose]; exact (d1SL F).property⟩

    -- We evaluate the multiplication d₁ᵀ * d₁ = 1 explicitly on the underlying matrices.
    -- This establishes the left-inverse property required to find the true inverse.
    have h_mul : d1T_SL * d1SL F = 1 := by
      apply Subtype.ext
      change (d1 F).transpose * d1 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [d1, Matrix.diagonal_apply, cons_val, Fin.reduceFinMk]

    -- Now, Aᵀ * A = 1 implies A⁻¹ = Aᵀ.
    have h_inv : (d1SL F)⁻¹ = d1T_SL := mul_eq_one_iff_inv_eq'.mp h_mul

    -- We map the equality down to the matrix level to apply the contragredient transformation.
    apply Subtype.ext
    change (((d1SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = d1 F

    -- Since A⁻¹ = Aᵀ, we substitute the inverse, and the double transpose cancels out: (Aᵀ)ᵀ = A.
    rw [h_inv]
    change ((d1 F).transpose).transpose = d1 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for d₂.
  have hd2 : invTransposeAutSL3 F (d2SL F) = d2SL F := by
    let d2T_SL : SL3 F := ⟨(d2 F).transpose, by rw [Matrix.det_transpose]; exact (d2SL F).property⟩
    have h_mul : d2T_SL * d2SL F = 1 := by
      apply Subtype.ext
      change (d2 F).transpose * d2 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [d2, Matrix.diagonal_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (d2SL F)⁻¹ = d2T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((d2SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = d2 F
    rw [h_inv]
    change ((d2 F).transpose).transpose = d2 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for d₃.
  have hd3 : invTransposeAutSL3 F (d3SL F) = d3SL F := by
    let d3T_SL : SL3 F := ⟨(d3 F).transpose, by rw [Matrix.det_transpose]; exact (d3SL F).property⟩
    have h_mul : d3T_SL * d3SL F = 1 := by
      apply Subtype.ext
      change (d3 F).transpose * d3 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [d3, Matrix.diagonal_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (d3SL F)⁻¹ = d3T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((d3SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = d3 F
    rw [h_inv]
    change ((d3 F).transpose).transpose = d3 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for the matrix w₁.
  have hw1 : invTransposeAutSL3 F (w1SL F) = w1SL F := by
    let w1T_SL : SL3 F := ⟨(w1 F).transpose, by rw [Matrix.det_transpose]; exact (w1SL F).property⟩
    have h_mul : w1T_SL * w1SL F = 1 := by
      apply Subtype.ext
      change (w1 F).transpose * w1 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [w1, Fin.sum_univ_three, of_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (w1SL F)⁻¹ = w1T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((w1SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = w1 F
    rw [h_inv]
    change ((w1 F).transpose).transpose = w1 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for the matrix w₂.
  have hw2 : invTransposeAutSL3 F (w2SL F) = w2SL F := by
    let w2T_SL : SL3 F := ⟨(w2 F).transpose, by rw [Matrix.det_transpose]; exact (w2SL F).property⟩
    have h_mul : w2T_SL * w2SL F = 1 := by
      apply Subtype.ext
      change (w2 F).transpose * w2 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [w2, Fin.sum_univ_three, of_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (w2SL F)⁻¹ = w2T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((w2SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = w2 F
    rw [h_inv]
    change ((w2 F).transpose).transpose = w2 F
    ext i j; rfl

  exact ⟨hd1, hd2, hd3, hw1, hw2⟩

/--
# Normalization of X₁₂ (Step 3)
Verifies **Step 3** of the main classification proof for automorphisms of `SL₃(F)`
(where `F` is a field of characteristic `≠ 2`). It proves that after prior diagonal
normalizations, we can successfully map the image of `x₁₂` to standard position.

## Proof Outline
From earlier steps, `X₁₂` is constrained to either `x₁₂(b)` or `x₂₁(c)`.
We evaluate the commutator relation `[X₁₂, X₂₃] = X₁₃` to restrict the constants:
1. **Case 1 (`X₁₂ = x₁₂(b)`):** Evaluating the commutator at entry `(0, 2)` forces `b² = b`.
   Since `F` is a field and `b ≠ 0`, `b = 1`. No further automorphisms are needed (`ε = false`).
2. **Case 2 (`X₁₂ = x₂₁(c)`):** Evaluating the commutator at entry `(2, 0)` forces `c² + c = 0`.
   Since `c ≠ 0`, `c = -1`. We then compose our map with the contragredient automorphism
   (`ε = true`), which preserves the base matrices (via `invTranspose_preserves_d_w`) and
   successfully flips `x₂₁(-1)` back to the standard `x₁₂(1)`.
-/
theorem x12_preserved (φ : AutSL3 F) : ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (x12SL F))) = x12SL F := by

  -- Get matrix g utilizing steps 1 and 2 for which the inner automorphism preserves
  -- d₁, ..., d₃, and w₁, ..., w₃. w₃ being preserved is given by w₁, and w₂ being
  -- preserved, so we don't assume anything about it.
  rcases w_preserved F φ with ⟨g, hd1, hd2, hd3, hw1, hw2⟩

  -- Define φ₂ as the inner automorphism by g.
  let φ2 : AutSL3 F := φ.trans (innerAutSL3byGL3 F g)

  have hd1_φ2 : φ2 (d1SL F) = d1SL F := hd1
  have hd2_φ2 : φ2 (d2SL F) = d2SL F := hd2
  have hd3_φ2 : φ2 (d3SL F) = d3SL F := hd3
  have hw1_φ2 : φ2 (w1SL F) = w1SL F := hw1
  have hw2_φ2 : φ2 (w2SL F) = w2SL F := hw2

  -- Denote X₁₂ as the image of x₁₂ under the current automorphism.
  -- We also denote it as (bᵢⱼ).
  let X12 := (φ2 (x12SL F)).val

  -- We first prove that X₁₂ commutes with d₃.
  -- This holds for x₁₂ and d₃, and since d₃ is fixed this follows.
  have h_comm_d3_X12 : (d3 F) * X12 = X12 * (d3 F) := by
    have h_comm_in_images: (φ2 (d3SL F * x12SL F)) = (φ2 (x12SL F * d3SL F)) := by
      -- We first prove that x₁₂ and d₃ commute.
      have h_comm_orig : d3SL F * x12SL F = x12SL F * d3SL F := by
        have h_matrix_comm : d3 F * x12 F = x12 F * d3 F := by
          rw [d3, x12, diagonal_fin_three, mul_fin_three, mul_fin_three]
          simp
        apply Subtype.ext h_matrix_comm
      rw [h_comm_orig]
    simp only [map_mul] at h_comm_in_images
    -- Use the fact that d₃ is fixed.
    rw [hd3_φ2] at h_comm_in_images
    -- Extract a matrix equality from the SL₃(F) matrix equality at h_inv_in_images.
    exact congrArg Subtype.val h_comm_in_images

  -- Commutativity with d₃ forces X₁₂ to be block-diagonal, with a 2x2 and a 1x1 block.
  have hX12_02 : X12 0 2 = 0 := by
    -- Matrices are functions, so entry-wise equality can be yielded by basic function facts.
    have h_entry : ((d3 F) * X12) 0 2 = (X12 * (d3 F)) 0 2 :=
      congrFun (congrFun h_comm_d3_X12 0) 2
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_if_eq_neg F h_entry.symm).symm

  have hX12_12 : X12 1 2 = 0 := by
    have h_entry : ((d3 F) * X12) 1 2 = (X12 * (d3 F)) 1 2 :=
      congrFun (congrFun h_comm_d3_X12 1) 2
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_if_eq_neg F h_entry.symm).symm

  have hX12_20 : X12 2 0 = 0 := by
    have h_entry : ((d3 F) * X12) 2 0 = (X12 * (d3 F)) 2 0 :=
      congrFun (congrFun h_comm_d3_X12 2) 0
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_if_eq_neg F h_entry).symm

  have hX12_21 : X12 2 1 = 0 := by
    have h_entry : ((d3 F) * X12) 2 1 = (X12 * (d3 F)) 2 1 :=
      congrFun (congrFun h_comm_d3_X12 2) 1
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_if_eq_neg F h_entry).symm

  -- Similarly to before, we now prove that conjugation by d₁ of X₁₂ is its inverse.
  have h_inv_d1_X12 : (d1 F) * X12 * (d1 F) * X12 = 1 := by
    have h_inv_in_images : φ2 (d1SL F * x12SL F * d1SL F * x12SL F) = φ2 1 := by
      have h_inv_orig : d1SL F * x12SL F * d1SL F * x12SL F = 1 := by
        have h_matrix_inv : d1 F * x12 F * d1 F * x12 F = 1 := by
          rw [d1, x12, diagonal_fin_three, one_fin_three, mul_fin_three, mul_fin_three, mul_fin_three]
          simp
        apply Subtype.ext h_matrix_inv
      rw [h_inv_orig]
    simp at h_inv_in_images
    rw [hd1_φ2] at h_inv_in_images
    exact congrArg Subtype.val h_inv_in_images

  -- Extract equations on X₁₂ entries via the equality d₁ * X₁₂ * d₁ * X₁₂ = 1.
  -- We first show what d₁ * X₁₂ * d₁ * X₁₂ is equal to entry-wise.
  have h_X12_matrix_eval : !![X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0, X12 0 0 * X12 0 1 - X12 0 1 * X12 1 1, 0;
                              -(X12 1 0 * X12 0 0) + X12 1 1 * X12 1 0, -(X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1, 0;
                              0, 0, X12 2 2 * X12 2 2] = d1 F * X12 * d1 F * X12 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [d1, of_apply, cons_val, Fin.reduceFinMk, hX12_02, hX12_12, hX12_20, hX12_21] <;>
      ring

  -- We now combine it with the fact that d₁ * X₁₂ * d₁ * X₁₂ = 1.
  have h_X12_eqs : !![X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0, X12 0 0 * X12 0 1 - X12 0 1 * X12 1 1, 0;
                      -(X12 1 0 * X12 0 0) + X12 1 1 * X12 1 0, -(X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1, 0;
                      0, 0, X12 2 2 * X12 2 2] = (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [h_X12_matrix_eval, h_inv_d1_X12]

  -- For future use, we extract these entry-equalities as theorems.
  have hX12_00 : X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0 = 1 := congrFun (congrFun h_X12_eqs 0) 0
  have hX12_01 : X12 0 0 * X12 0 1 - X12 0 1 * X12 1 1 = 0 := congrFun (congrFun h_X12_eqs 0) 1
  have hX12_10 : -(X12 1 0 * X12 0 0) + X12 1 1 * X12 1 0 = 0 := congrFun (congrFun h_X12_eqs 1) 0
  have hX12_11 : -(X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1 = 1 := congrFun (congrFun h_X12_eqs 1) 1
  have hX12_22 : X12 2 2 * X12 2 2 = 1 := congrFun (congrFun h_X12_eqs 2) 2

  -- We now prove b₁₁ = b₂₂.
  -- We first need the following helper lemma, which we will also need later in the proof.
  have h_diag_gives_contra : (X12 0 1 = 0 ∧ X12 1 0 = 0) → False := by
    rintro ⟨hb12_zero, hb21_zero⟩

    -- Substitute b₁₂ = 0 and b₂₁ = 0 back into our equations, yielding that b₁₁² = b₂₂² = 1.
    have hb11_sq : X12 0 0 * X12 0 0 = 1 := by
      calc X12 0 0 * X12 0 0
        _ = X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0 := by rw [hb12_zero, zero_mul, sub_zero]
        _ = 1 := hX12_00

    have hb22_sq : X12 1 1 * X12 1 1 = 1 := by
      calc X12 1 1 * X12 1 1
        _ = - (X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1 := by rw [hb12_zero, zero_mul, neg_zero, zero_add]
        _ = 1 := hX12_11

    -- We now have that X₁₂ is diagonal with entries whose squares are 1 on the diagonal.
    -- Hence it has order 2. To be more exact, we only need to show it becomes I when squared.
    -- Showing that this is true is done by a quick calculation.
    have h_X12_sq : X12 * X12 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, hX12_02, hX12_12, hX12_20, hX12_21, hb12_zero, hb21_zero]
      · exact hb11_sq
      · exact hb22_sq
      · exact hX12_22

    -- Automorphisms preserve identities like a matrix having its square be 1, since 1 is preserved.
    have h_x12_sq_eq_1 : x12 F * x12 F = 1 := by
      have h_image_sq : φ2 (x12SL F) * φ2 (x12SL F) = 1 := Subtype.ext h_X12_sq
      rw [← map_mul, ← map_one φ2] at h_image_sq
      -- Since φ2 is an automorphism, it is injective, the inputs must be equal.
      have h_sl3_sq : x12SL F * x12SL F = 1 := EquivLike.injective φ2 h_image_sq
      -- Extract the raw matrices equality.
      exact congrArg Subtype.val h_sl3_sq

    -- Yield a contradiction since x₁₂ square is not 1.
    have h_two_eq_zero : (2 : F) = 0 := by
      have h_eval : (x12 F * x12 F) 0 1 = (1 : Matrix (Fin 3) (Fin 3) F) 0 1 :=
        congrFun (congrFun h_x12_sq_eq_1 0) 1
      simp [x12, Matrix.mul_apply, Fin.sum_univ_three] at h_eval
      -- h_eval reduces to 1+1 = 0
      linear_combination h_eval

    exact absurd h_two_eq_zero two_ne_zero

  -- We can now show b₁₁ = b₂₂.
  have hb11_eq_b22 : X12 0 0 = X12 1 1 := by
    -- Assume in contradiction this isn't the case.
    by_contra h_neq
    have h_diff_ne_zero : X12 0 0 - X12 1 1 ≠ 0 := sub_ne_zero.mpr h_neq
    have hX12_01_factored : X12 0 1 * (X12 0 0 - X12 1 1) = 0 := by linear_combination hX12_01

    -- F is a field, and in particular an integral domain.
    -- Therefore if a product is 0, and one of the multiplied elements is not 0, the other must be 0. Hence b₁₂ is 0.
    have hb12_zero : X12 0 1 = 0 := (mul_eq_zero.mp hX12_01_factored).resolve_right h_diff_ne_zero

    -- Similarly one shows that b₂₁ is 0.
    have hX12_10_factored : X12 1 0 * (X12 1 1 - X12 0 0) = 0 := by linear_combination hX12_10
    have h_diff2_ne_zero : X12 1 1 - X12 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h_neq)
    have hb21_zero : X12 1 0 = 0 := (mul_eq_zero.mp hX12_10_factored).resolve_right h_diff2_ne_zero

    -- We get a contradiction using our helper lemma.
    exact h_diag_gives_contra ⟨hb12_zero, hb21_zero⟩

  -- Using determinants, we can also get that b₃₃ is 1.
  have hb33_eq_1 : X12 2 2 = 1 := by
    have h_det : X12.det = 1 := (φ2 (x12SL F)).property
    -- Expand determinant.
    rw [Matrix.det_fin_three] at h_det
    -- Equalities on X₁₂'s entries allow us to simplify this determinant.
    simp [hX12_02, hX12_12, hX12_20, hX12_21] at h_det
    rw [← mul_sub_right_distrib, ← hb11_eq_b22, hX12_00, one_mul] at h_det
    exact h_det

  -- We now calculate the image of x₁₃ in terms of X₁₂.
  -- We first introduce X₁₃ as this image.
  let X13 := (φ2 (x13SL F)).val

  -- The proof of what X₁₃ looks like is divided into several parts.
  -- We first show some equation on x₁₃⁻¹ in terms of other matrices.
  -- We then apply Φ₂ on it, and use this to find explicitly the coordinates of X₁₃⁻¹ in terms of the coordinates of X₁₂.
  -- Finally we just take the inverse of that matrix to get the desired form of X₁₃.

  -- We first show that x₁₃ * w₂ * x₁₂ = w₂.
  have h_x13_w2_x12 : x13SL F * w2SL F * x12SL F = w2SL F := by
    -- It suffices to prove this for the underlying matrices. This is a simple product calculation.
    have h_mat : x13 F * w2 F * x12 F = w2 F := by
      rw [x13, w2, x12, mul_fin_three, mul_fin_three]
      simp
    apply Subtype.ext h_mat

  -- Getting the initial equality now follows from an elementary group calculation.
  have h_w2_x12_conj : w2SL F * x12SL F * (w2SL F)⁻¹ = (x13SL F)⁻¹ := by
    -- Move x₁₃ to the other side.
    apply mul_left_cancel (a := x13SL F)
    -- We now apply the fact that x₁₃ * w₂ * x₁₂ = w₂ to simplify the left-hand side.
    rw [← mul_assoc, ← mul_assoc, h_x13_w2_x12]
    simp

  -- We would like to now apply Φ₂ to this equation to calculate the terms of the inverse of X₁₃.
  -- We first need to calculate w₂'s inverse however, as it appears on the left-hand-side.
  have h_w2_inv : (w2SL F)⁻¹ = w2SL F * d1SL F := by
    -- Prove w₂ * (w₂ * d₁) = 1.
    have h_mul : w2SL F * (w2SL F * d1SL F) = 1 := by
      have h_mat : w2 F * (w2 F * d1 F) = 1 := by
        rw [w2, d1, diagonal_fin_three, one_fin_three, mul_fin_three, mul_fin_three]
        simp
      apply Subtype.ext h_mat
    rw [mul_eq_one_iff_inv_eq', inv_eq_iff_eq_inv] at h_mul
    exact h_mul.symm

  -- Let us now apply Φ₂ to get an equality on X₁₃⁻¹.
  let X13_inv := (φ2 (x13SL F)⁻¹).val

  have h_X13_inv_eq : X13_inv = w2 F * X12 * (w2 F * d1 F) := by
    -- Applying Φ₂ gives the following equality at first.
    have h_img : φ2 (x13SL F)⁻¹ = φ2 (w2SL F * x12SL F * (w2SL F)⁻¹) := congrArg φ2 h_w2_x12_conj.symm
    -- We may now simplify it.
    simp at h_img
    rw [← map_inv] at h_img
    rw [hw2_φ2, h_w2_inv] at h_img

    -- We now move this SL₃ matrices equality to matrix equality, and by simply substituting
    -- the elements in this equality by the notation for them, we are done.
    have h_img_mat := congrArg Subtype.val h_img

    calc X13_inv
      _ = (φ2 ((x13SL F)⁻¹)).val := rfl
      _ = (w2SL F * φ2 (x12SL F) * (w2SL F * d1SL F)).val := h_img_mat
      _ = (w2SL F * φ2 (x12SL F)).val * (w2SL F * d1SL F).val := by rw [SpecialLinearGroup.coe_mul]
      _ = (w2SL F).val * (φ2 (x12SL F)).val * ((w2SL F).val * (d1SL F).val) := by rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
      _ = w2 F * X12 * (w2 F * d1 F) := rfl

  -- Using the established equality on X₁₃⁻¹,
  -- we can calculate all its entries in terms of those of X₁₂.
  have h_X13inv_mat : X13_inv =
      !![ X12 0 0, 0, -X12 0 1;
                0, 1,        0;
         -X12 1 0, 0,  X12 1 1] := by
    rw [h_X13_inv_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [w2, d1, of_apply, cons_val, Fin.reduceFinMk,
            hX12_02, hX12_12, hX12_20, hX12_21, hb33_eq_1]

  -- Let us now calculate the entries matrix X₁₃, which is the inverse of X₁₃⁻¹.
  -- We first show that the entries we want form an inverse matrix.
  -- We slightly rearrange elements for this.
  have h11_sub : X12 1 1 * X12 1 1 = 1 + X12 0 1 * X12 1 0 := by linear_combination hX12_11
  have h_X13_target_mul_inv : !![X12 0 0, 0, X12 0 1;
                                       0, 1,       0;
                                 X12 1 0, 0, X12 1 1] * X13_inv = 1 := by
    rw [h_X13inv_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
      simp [of_apply, cons_val, Fin.reduceFinMk, hb11_eq_b22, h11_sub] <;>
      ring

  -- We now establish that X₁₃⁻¹ * X₁₃ = 1 as well.
  -- This is entirely trivial, but since X13_inv isn't defined for this
  -- to be exactly immediate we need to do a small calculation.
  have h_inv_mul_X13 : X13_inv * X13 = 1 := by
    calc X13_inv * X13
      _ = (φ2 ((x13SL F)⁻¹)).val * (φ2 (x13SL F)).val := rfl
      _ = (φ2 ((x13SL F)⁻¹) * φ2 (x13SL F)).val := by rw [← SpecialLinearGroup.coe_mul]
      _ = (φ2 ((x13SL F)⁻¹ * x13SL F)).val := by rw [← map_mul]
      _ = (φ2 1).val := by rw [inv_mul_cancel]
      _ = (1 : SL3 F).val := by rw [map_one]
      _ = 1 := rfl

  -- We now get the desired equality for X₁₃.
  have h_X13_mat : X13 = !![X12 0 0, 0, X12 0 1;
                                  0, 1,       0;
                            X12 1 0, 0, X12 1 1] := by
    calc X13
      _ = 1 * X13 := by rw [Matrix.one_mul]
      _ = (!![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] * X13_inv) * X13 := by
        rw [h_X13_target_mul_inv]
      _ = !![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] * (X13_inv * X13) := by
        rw [Matrix.mul_assoc]
      _ = !![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] * 1 := by rw [h_inv_mul_X13]
      _ = !![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] := by rw [Matrix.mul_one]

  have hX13_00 : X13 0 0 = X12 0 0 := congrFun (congrFun h_X13_mat 0) 0
  have hX13_01 : X13 0 1 = 0       := congrFun (congrFun h_X13_mat 0) 1
  have hX13_02 : X13 0 2 = X12 0 1 := congrFun (congrFun h_X13_mat 0) 2
  have hX13_10 : X13 1 0 = 0       := congrFun (congrFun h_X13_mat 1) 0
  have hX13_11 : X13 1 1 = 1       := congrFun (congrFun h_X13_mat 1) 1
  have hX13_12 : X13 1 2 = 0       := congrFun (congrFun h_X13_mat 1) 2
  have hX13_20 : X13 2 0 = X12 1 0 := congrFun (congrFun h_X13_mat 2) 0
  have hX13_21 : X13 2 1 = 0       := congrFun (congrFun h_X13_mat 2) 1
  have hX13_22 : X13 2 2 = X12 1 1 := congrFun (congrFun h_X13_mat 2) 2

  -- The next step is now showing that X₁₂ and X₁₃ commute.
  -- This is as they are images of commuting matrices in a homomorphism.
  have h_x12_x13_comm_mat : x12 F * x13 F = x13 F * x12 F := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [x12, x13, of_apply, cons_val, Fin.reduceFinMk]

  -- We have shown that x₁₂ and x₁₃ commute on a matrix level.
  -- Let us lift it to an SL₃ equality.
  have h_x12SL_x13SL_comm : x12SL F * x13SL F = x13SL F * x12SL F := Subtype.ext h_x12_x13_comm_mat

  -- Using the fact that X₁₂ and X₁₃ are images of commuting matrices we are done.
  have h_X12_X13_comm : X12 * X13 = X13 * X12 := by
    calc X12 * X13
      _ = (φ2 (x12SL F)).val * (φ2 (x13SL F)).val := rfl
      _ = (φ2 (x12SL F) * φ2 (x13SL F)).val := by rw [← SpecialLinearGroup.coe_mul]
      _ = (φ2 (x12SL F * x13SL F)).val := by rw [← map_mul]
      _ = (φ2 (x13SL F * x12SL F)).val := by rw [h_x12SL_x13SL_comm]
      _ = (φ2 (x13SL F) * φ2 (x12SL F)).val := by rw [map_mul]
      _ = (φ2 (x13SL F)).val * (φ2 (x12SL F)).val := by rw [SpecialLinearGroup.coe_mul]
      _ = X13 * X12 := rfl

  -- This means that the commutator X₁₂ * X₁₃ - X₁₃ * X₁₂ = 0.
  -- This is useful since explicitly calculating
  -- X₁₂ * X₁₃ - X₁₃ * X₁₂ yields more equations on the entries of X₁₂.
  have h_X12_X13_sub_eq_zero : X12 * X13 - X13 * X12 = 0 := by rw [h_X12_X13_comm, sub_self]

  -- We now evaluate the commutator X₁₂ * X₁₃ - X₁₃ * X₁₂ explicitly as a matrix.
  have h_comm_matrix_eval : !![0, X12 0 1 - X12 0 0 * X12 0 1, X12 0 0 * X12 0 1 - X12 0 1;
                               X12 1 0 * X12 0 0 - X12 1 0, 0, X12 1 0 * X12 0 1;
                               X12 1 0 - X12 1 0 * X12 0 0, -(X12 1 0 * X12 0 1), 0] =
                               X12 * X13 - X13 * X12 := by
    rw [h_X13_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [of_apply, cons_val, Fin.reduceFinMk, hX12_02, hX12_12,
            hX12_20, hX12_21, hb33_eq_1, hb11_eq_b22]

  -- We have proved that the commutator is zero, yielding the following matrix equality.
  have h_comm_eqs : !![0, X12 0 1 - X12 0 0 * X12 0 1, X12 0 0 * X12 0 1 - X12 0 1;
                       X12 1 0 * X12 0 0 - X12 1 0, 0, X12 1 0 * X12 0 1;
                       X12 1 0 - X12 1 0 * X12 0 0, -(X12 1 0 * X12 0 1), 0] =
                       (0 : Matrix (Fin 3) (Fin 3) F) := by
    rw [h_comm_matrix_eval, h_X12_X13_sub_eq_zero]

  -- We hence get the following six equations.
  have h_comm_01 : X12 0 1 - X12 0 0 * X12 0 1 = 0 := congrFun (congrFun h_comm_eqs 0) 1
  have h_comm_02 : X12 0 0 * X12 0 1 - X12 0 1 = 0 := congrFun (congrFun h_comm_eqs 0) 2
  have h_comm_10 : X12 1 0 * X12 0 0 - X12 1 0 = 0 := congrFun (congrFun h_comm_eqs 1) 0
  have h_comm_12 : X12 1 0 * X12 0 1 = 0          := congrFun (congrFun h_comm_eqs 1) 2
  have h_comm_20 : X12 1 0 - X12 1 0 * X12 0 0 = 0 := congrFun (congrFun h_comm_eqs 2) 0
  have h_comm_21 : -(X12 1 0 * X12 0 1) = 0       := congrFun (congrFun h_comm_eqs 2) 1

  -- Using these equations, we get that b₁₁, b₂₂ = 1.
  -- We first need the following lemma, which as we will see is useful in its own right.
  have h_b12_zero_b21_nonzero_or_symm : (X12 0 1 = 0 ∧ X12 1 0 ≠ 0) ∨
                                        (X12 1 0 = 0 ∧ X12 0 1 ≠ 0) := by
    rcases mul_eq_zero.mp h_comm_12 with h21 | h12
    · right
      exact ⟨h21, fun h12_zero => h_diag_gives_contra ⟨h12_zero, h21⟩⟩
    · left
      exact ⟨h12, fun h21_zero => h_diag_gives_contra ⟨h12, h21_zero⟩⟩

  -- This allows us to prove the desired equality b₁₁ = 1.
  have h_b11_eq_1 : X12 0 0 = 1 := by
    rcases h_b12_zero_b21_nonzero_or_symm with ⟨_, h21_nonzero⟩ | ⟨_, h12_nonzero⟩
    · have h_sub : X12 1 0 * (X12 0 0 - 1) = 0 := by
        calc X12 1 0 * (X12 0 0 - 1)
          _ = X12 1 0 * X12 0 0 - X12 1 0 := by ring
          _ = 0 := h_comm_10
      -- Since b₂₁ ≠ 0, it must be that b₁₁ - 1 = 0.
      exact sub_eq_zero.mp ((mul_eq_zero.mp h_sub).resolve_left h21_nonzero)
    · have h_sub : (1 - X12 0 0) * X12 0 1 = 0 := by
        calc (1 - X12 0 0) * X12 0 1
          _ = X12 0 1 - X12 0 0 * X12 0 1 := by ring
          _ = 0 := h_comm_01
      have h_one_sub : 1 - X12 0 0 = 0 := (mul_eq_zero.mp h_sub).resolve_right h12_nonzero
      exact (sub_eq_zero.mp h_one_sub).symm

  -- We therefore are in one of two cases:
  -- Either X₁₂ is x₁₂(b) for nonzero b, or it is x₂₁(c) for nonzero c.
  have h_b22_eq_1 : X12 1 1 = 1 := by rw [← hb11_eq_b22, h_b11_eq_1]
  have h_X12_shape : X12 = !![      1, X12 0 1, 0;
                              X12 1 0,       1, 0;
                                    0,       0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h_b11_eq_1, h_b22_eq_1, hb33_eq_1, hX12_02, hX12_12, hX12_20, hX12_21]

  have h_X12_is_specific_transvection :
    (∃ b : F, b ≠ 0 ∧ X12 = !![1, b, 0; 0, 1, 0; 0, 0, 1]) ∨
    (∃ c : F, c ≠ 0 ∧ X12 = !![1, 0, 0; c, 1, 0; 0, 0, 1]) := by
    rcases h_b12_zero_b21_nonzero_or_symm with ⟨hb12_zero, hb21_nonzero⟩ | ⟨hb21_zero, hb12_nonzero⟩
    · right
      exact ⟨X12 1 0, hb21_nonzero, by rw [hb12_zero] at h_X12_shape; exact h_X12_shape⟩
    · left
      exact ⟨X12 0 1, hb12_nonzero, by rw [hb21_zero] at h_X12_shape; exact h_X12_shape⟩

  -- Before embarking on our division into cases,
  -- we first express the image X₂₃ in terms of that of X₁₃.
  -- To do that, first we prove the equality as a simple matrix multiplication (w₁ * x₂₃ = x₁₃ * w₁)
  have h_w1_x23 : w1SL F * x23SL F = x13SL F * w1SL F := by
    have h_mat : w1 F * x23 F = x13 F * w1 F := by
      rw [w1, x23, x13, mul_fin_three, mul_fin_three]
      simp
    apply Subtype.ext h_mat

  -- We now rearrange to get x₂₃ = w₁⁻¹ * x₁₃ * w₁ in SL₃(F).
  have h_w1_inv_x13_w1 : x23SL F = (w1SL F)⁻¹ * x13SL F * w1SL F := by
    calc x23SL F
      _ = (w1SL F)⁻¹ * (w1SL F * x23SL F) := by rw [inv_mul_cancel_left]
      _ = (w1SL F)⁻¹ * (x13SL F * w1SL F) := by rw [h_w1_x23]
      _ = (w1SL F)⁻¹ * x13SL F * w1SL F := by rw [mul_assoc]

  -- Before applying Φ₂ and getting an equality for X₂₃, we first want to realize what w₁⁻¹ is.
  have h_w1_inv : (w1SL F)⁻¹ = w1SL F * d3SL F := by
    have h_mul : w1SL F * (w1SL F * d3SL F) = 1 := by
      have h_mat : w1 F * (w1 F * d3 F) = 1 := by
        rw [w1, d3, diagonal_fin_three, one_fin_three, mul_fin_three, mul_fin_three]
        simp
      apply Subtype.ext h_mat
    rw [mul_eq_one_iff_inv_eq', inv_eq_iff_eq_inv] at h_mul
    exact h_mul.symm

  -- Define X₂₃ as the image under Φ₂.
  let X23 := (φ2 (x23SL F)).val

  -- Map the SL₃ equality through the homomorphism Φ₂ and then down to a matrix equality.
  have h_X23_eq : X23 = (w1 F * d3 F) * X13 * w1 F := by
    have h_img : φ2 (x23SL F) = (w1SL F * d3SL F) * φ2 (x13SL F) * w1SL F := by
      calc φ2 (x23SL F)
        _ = φ2 ((w1SL F)⁻¹ * x13SL F * w1SL F) := by rw [h_w1_inv_x13_w1]
        _ = φ2 ((w1SL F)⁻¹) * φ2 (x13SL F) * φ2 (w1SL F) := by rw [map_mul, map_mul]
        _ = (φ2 (w1SL F))⁻¹ * φ2 (x13SL F) * φ2 (w1SL F) := by rw [map_inv]
        _ = (w1SL F)⁻¹ * φ2 (x13SL F) * w1SL F := by rw [hw1_φ2]
        _ = (w1SL F * d3SL F) * φ2 (x13SL F) * w1SL F := by rw [h_w1_inv]

    have h_img_mat := congrArg Subtype.val h_img
    calc X23
      _ = (φ2 (x23SL F)).val := rfl
      _ = ((w1SL F * d3SL F) * φ2 (x13SL F) * w1SL F).val := h_img_mat
      _ = ((w1SL F * d3SL F) * φ2 (x13SL F)).val * (w1SL F).val := by
        rw [SpecialLinearGroup.coe_mul]
      _ = (w1SL F * d3SL F).val * (φ2 (x13SL F)).val * (w1SL F).val := by
        rw [SpecialLinearGroup.coe_mul]
      _ = ((w1SL F).val * (d3SL F).val) * X13 * (w1SL F).val := by
        rw [SpecialLinearGroup.coe_mul]
      _ = (w1 F * d3 F) * X13 * w1 F := rfl

  -- We can now explicitly calculate the right hand side of the above, yielding the following.
  have h_X23_mat : X23 = !![1,       0, 0;
                            0,       1, X12 0 1;
                            0, X12 1 0, 1] := by
    rw [h_X23_eq, h_X13_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [w1, d3, of_apply, cons_val, Fin.reduceFinMk, h_b11_eq_1, h_b22_eq_1]

  -- Extract entry equations from the above.
  have hX23_00 : X23 0 0 = 1       := congrFun (congrFun h_X23_mat 0) 0
  have hX23_01 : X23 0 1 = 0       := congrFun (congrFun h_X23_mat 0) 1
  have hX23_02 : X23 0 2 = 0       := congrFun (congrFun h_X23_mat 0) 2
  have hX23_10 : X23 1 0 = 0       := congrFun (congrFun h_X23_mat 1) 0
  have hX23_11 : X23 1 1 = 1       := congrFun (congrFun h_X23_mat 1) 1
  have hX23_12 : X23 1 2 = X12 0 1 := congrFun (congrFun h_X23_mat 1) 2
  have hX23_20 : X23 2 0 = 0       := congrFun (congrFun h_X23_mat 2) 0
  have hX23_21 : X23 2 1 = X12 1 0 := congrFun (congrFun h_X23_mat 2) 1
  have hX23_22 : X23 2 2 = 1       := congrFun (congrFun h_X23_mat 2) 2

  -- We would also like to, before starting the division into cases, show that [X₁₂, X₂₃] = X₁₃.
  -- More precisely, we show that a rearranging of this equation holds.
  -- We start with proving that [x₁₂(1), x₂₃(1)] = x₁₃(1),
  -- and again more precisely x₁₂ * x₂₃ = x₁₃ * x₂₃ * x₁₂.
  have h_x12_x23_comm_rel : x12SL F * x23SL F = x13SL F * x23SL F * x12SL F := by
    have h_mat : x12 F * x23 F = x13 F * x23 F * x12 F := by
      rw [x12, x23, x13, mul_fin_three, mul_fin_three, mul_fin_three]
      simp
    apply Subtype.ext h_mat

  -- We now push this relation through the homomorphism Φ₂ to get the result.
  have h_X12_X23_comm_rel : X12 * X23 = X13 * X23 * X12 := by
    have h_img : φ2 (x12SL F * x23SL F) = φ2 (x13SL F * x23SL F * x12SL F) :=
      congrArg φ2 h_x12_x23_comm_rel
    have h_LHS : (φ2 (x12SL F * x23SL F)).val = X12 * X23 := by
      rw [map_mul, SpecialLinearGroup.coe_mul]
    have h_RHS : (φ2 (x13SL F * x23SL F * x12SL F)).val = X13 * X23 * X12 := by
      rw [map_mul, map_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
    rw [← h_LHS, ← h_RHS, h_img]

  -- Finally, we may start the division into cases.
  rcases h_X12_is_specific_transvection with ⟨b, hb_neq_0, hX12_b⟩ | ⟨c, hc_neq_0, hX12_c⟩

  /-
  ======================================================================
    CASE 1: X₁₂ is x₁₂(b)
  ======================================================================
  In this branch, X₁₂ is already a transvection with the correct position.
  We evaluate the commutator relation X₁₂ * X₂₃ = X₁₃ * X₂₃ * X₁₂ in accordance.
  We evaluate specifically at the entry (0, 2) to extract the algebraic
  relation for b without expanding the full 3x3 matrices.
  -/
  · have h_entry_eq : (X12 * X23) 0 2 = (X13 * X23 * X12) 0 2 := congrFun
      (congrFun h_X12_X23_comm_rel 0) 2

    -- Evaluate the Left Hand Side of the above at (0, 2).
    have h_LHS_eval : (X12 * X23) 0 2 = b * b := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_b, h_X23_mat, of_apply, cons_val]

    -- Evaluate the Right Hand Side of the above at (0, 2).
    have h_RHS_eval : (X13 * X23 * X12) 0 2 = b := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_b, h_X13_mat, h_X23_mat, of_apply, cons_val]

    -- By combining these, we deduce the explicit relation b² = b.
    have h_b_sq_eq_b : b * b = b := by rw [← h_LHS_eval, h_entry_eq, h_RHS_eval]

    -- Since F is a field (and thus an integral domain) and b ≠ 0, b² = b uniquely forces b = 1.
    have hb_eq_1 : b = 1 := by
      have h_sub : b * (b - 1) = 0 := by
        calc b * (b - 1)
          _ = b * b - b := by ring
          _ = b - b := by rw [h_b_sq_eq_b]
          _ = 0 := by ring
      have hb_sub_1 : b - 1 = 0 := (mul_eq_zero.mp h_sub).resolve_left hb_neq_0
      exact sub_eq_zero.mp hb_sub_1

    -- Substitute b = 1 back into our shape for X₁₂ to definitively prove X₁₂ = x₁₂(1).
    have h_X12_eq_x12 : X12 = x12 F := by
      rw [hb_eq_1] at hX12_b
      rw [hX12_b, FieldAutomorphisms.x12]

    -- Convert the matrix equality back to an SL₃ equality mapped by φ₂.
    have h_x12_preserved_φ2 : φ2 (x12SL F) = x12SL F := Subtype.ext h_X12_eq_x12

    -- To complete the existential goal for this case:
    -- X₁₂ is already mapped to itself, so we do not need the contragredient automorphism.
    -- Hence we provide `false` for ε, mapping to the identity automorphism.
    use g, false
    simp only [graphChoiceSL3]
    exact ⟨hd1_φ2, hd2_φ2, hd3_φ2, hw1_φ2, hw2_φ2, h_x12_preserved_φ2⟩

  /-
  ======================================================================
    CASE 2: X₁₂ is x₂₁(c)
  ======================================================================
  In this branch, the change of basis left X₁₂ on the lower diagonal.
  We must extract the constant c, verify c = -1, and deploy the
  contragredient automorphism (invTransposeMap) to restore standardness.
  -/
  · -- We evaluate the commutator relation X₁₂ * X₂₃ = X₁₃ * X₂₃ * X₁₂.
    -- We evaluate specifically at the entry (2, 0) to extract the algebraic relation for c.
    have h_entry_eq : (X12 * X23) 2 0 = (X13 * X23 * X12) 2 0 :=
      congrFun (congrFun h_X12_X23_comm_rel 2) 0

    -- Evaluate the Left Hand Side at (2, 0).
    have h_LHS_eval : (X12 * X23) 2 0 = 0 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_c, h_X23_mat, of_apply, cons_val]

    -- Evaluate the Right Hand Side at (2, 0).
    have h_RHS_eval : (X13 * X23 * X12) 2 0 = c * c + c := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_c, h_X13_mat, h_X23_mat, of_apply, cons_val]
      ring

    -- By combining these, we deduce the relation c² + c = 0.
    have h_c_sq_add_c : c * c + c = 0 := by rw [← h_RHS_eval, ← h_entry_eq, h_LHS_eval]

    -- Since F is a field and c ≠ 0, factoring c(c + 1) = 0 forces c = -1.
    have hc_eq_neg_1 : c = -1 := by
      have h_sub : c * (c + 1) = 0 := by
        calc c * (c + 1)
          _ = c * c + c := by ring
          _ = 0 := h_c_sq_add_c
      have hc_add_1 : c + 1 = 0 := (mul_eq_zero.mp h_sub).resolve_left hc_neq_0
      calc c = c + 1 - 1 := by ring
           _ = 0 - 1 := by rw [hc_add_1]
           _ = -1 := by ring

    -- Substitute c = -1 back into our shape for X₁₂ to prove X₁₂ = x₂₁(-1).
    have h_X12_eq_x21_neg1 : X12 = !![ 1, 0, 0;
                                      -1, 1, 0;
                                       0, 0, 1] := by
      rw [hc_eq_neg_1] at hX12_c
      exact hX12_c

    -- Because X₁₂ = x₂₁(-1), x₁₂(1) does not natively map to itself.
    -- We must compose our current map with the contragredient transformation (Φ₃).
    -- We utilize our prior theorem to securely show that this map preserves d₁, d₂, d₃, w₁, and w₂.
    rcases invTranspose_preserves_d_w F with ⟨h_invT_d1, h_invT_d2, h_invT_d3, h_invT_w1, h_invT_w2⟩

    have h_phi3_d1 : graphChoiceSL3 F true (φ2 (d1SL F)) = d1SL F := by rw [hd1_φ2]; exact h_invT_d1
    have h_phi3_d2 : graphChoiceSL3 F true (φ2 (d2SL F)) = d2SL F := by rw [hd2_φ2]; exact h_invT_d2
    have h_phi3_d3 : graphChoiceSL3 F true (φ2 (d3SL F)) = d3SL F := by rw [hd3_φ2]; exact h_invT_d3
    have h_phi3_w1 : graphChoiceSL3 F true (φ2 (w1SL F)) = w1SL F := by rw [hw1_φ2]; exact h_invT_w1
    have h_phi3_w2 : graphChoiceSL3 F true (φ2 (w2SL F)) = w2SL F := by rw [hw2_φ2]; exact h_invT_w2

    -- Finally, we apply the contragredient automorphism to X₁₂ = x₂₁(-1) to flip it to x₁₂(1).
    -- We isolate the explicit Matrix inversion away from the opaque SL₃ inversion.
    let x21_pos1_SL : SL3 F := ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by
      simp [Matrix.det_fin_three, of_apply, cons_val]⟩

    -- We prove that the above matrix is the inverse of X12.
    -- As its transpose is x₁₂(1), we will be done.
    have h_mat_mul : !![1, 0, 0; 1, 1, 0; 0, 0, 1] * X12 = 1 := by
      rw [h_X12_eq_x21_neg1]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply] <;>
        simp [Fin.sum_univ_three, of_apply, cons_val, Fin.reduceFinMk]

    have hX12_mul_inv : x21_pos1_SL * φ2 (x12SL F) = 1 := Subtype.ext h_mat_mul
    have hX12_inv : (φ2 (x12SL F))⁻¹ = x21_pos1_SL := mul_eq_one_iff_inv_eq'.mp hX12_mul_inv

    -- We step the goal down to the matrix definitions, apply the known inverse,
    -- and let the transpose physically flip x₂₁(-1) to x₁₂(1).
    have h_phi3_x12 : graphChoiceSL3 F true (φ2 (x12SL F)) = x12SL F := by
      change invTransposeMap F (φ2 (x12SL F)) = x12SL F
      apply Subtype.ext
      change (((φ2 (x12SL F))⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = x12 F
      rw [hX12_inv]
      change (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).transpose = x12 F
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [FieldAutomorphisms.x12, Matrix.transpose_apply, of_apply, cons_val, Fin.reduceFinMk]

    -- Provide the witness utilizing ε = true to deploy the contragredient automorphism mapping.
    use g, true
    exact ⟨h_phi3_d1, h_phi3_d2, h_phi3_d3, h_phi3_w1, h_phi3_w2, h_phi3_x12⟩


def IsTransvectionSL3 (x : SL3 R) : Prop :=
  ∃ i j : Fin 3, ∃ c : R,
    i ≠ j ∧
    (x : Matrix (Fin 3) (Fin 3) R) =
      Matrix.transvection i j c

theorem transv_to_transv_same_coeff (φ : AutSL3 (R)) :
(φ (d1SL R)  = d1SL R ∧
φ (d2SL R)  = d2SL R ∧
φ (d3SL R)  = d3SL R ∧
φ (w1SL R) = w1SL R ∧
φ (w2SL R) = w2SL R ∧
φ (x12SL R) = x12SL R) → ∃ (f : R ≃+* R), ∀ (E : SL3 R) , (IsTransvectionSL3 R E) → φ E = E.map f:= by sorry




theorem field_class
    (φ : AutSL3 F) :
    ∃ (σ : F ≃+* F) (ε : Bool) (g : GL (Fin 3) F),
      ∀ (x : SL3 F),
        φ x =
            ringAutSL3 F σ ((graphChoiceSL3 F ε) (innerAutSL3byGL3 F g x))
             := by
  sorry

end FieldAutomorpisms
