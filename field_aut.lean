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
    simp only [Matrix.transpose_transpose]
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
    simp only [Matrix.transpose_transpose]

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
                simp only [cons_val, mul_zero, mul_neg, mul_one, neg_zero, add_zero, neg_neg,
                          zero_add]
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd3] at this
          simp only [v1]
          nth_rw 2 [← this]
          exact ext fun i => congrFun rfl
        rw [d3, diagonal_fin_three] at this
        nth_rw 10 [← this, eta_fin_three v1]
        simp only [cons_val, cons_mul, vecMul_cons, head_cons, one_smul, tail_cons, zero_smul,
                   empty_vecMul, add_zero, neg_smul, neg_cons, zero_add, empty_mul,
                   Equiv.symm_apply_apply, smul_cons, smul_eq_mul, mul_one, mul_zero, mul_neg,
                   add_cons, empty_add_empty, neg_zero, neg_neg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, of_apply, cons_val]
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
                simp only [cons_val, cons_mul, vecMul_cons, head_cons, zero_smul, tail_cons,
                          one_smul, zero_add, neg_smul, neg_cons, neg_zero, neg_empty, empty_mul]
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd2, hd1] at this
          rw [← SpecialLinearGroup.coe_mul, this]
          rfl
        exact this
      rw [d1, d2, diagonal_fin_three, diagonal_fin_three, ← first_rep] at this
      simp only [cons_val, cons_mul, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_one,
                mul_zero, smul_empty, tail_cons, mul_neg, zero_smul, empty_vecMul, add_zero,
                add_cons, zero_add, empty_add_empty, empty_mul, neg_smul, one_smul, neg_cons,
                neg_zero, neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true,
                true_and] at this
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, of_apply, cons_val]
      · exact (zero_iff_eq_neg_self _).mpr this.left
      · exact (zero_iff_eq_neg_self _).mpr this.right.symm
    have det_v1: det v1 = 1 := by
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v101: IsUnit (v1 0 1) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, det_fin_three] at det_v1
      simp only [of_apply, cons_val, zero_mul, sub_self, add_zero, zero_ne_one] at det_v1
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
              simp only [cons_val, mul_zero, mul_neg, mul_one, zero_add, add_zero, neg_zero]
            apply Subtype.ext this
          rw [this]
        rw [map_mul, map_mul, hd3] at this
        simp only [v1]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      rw [← second_rep, d3, diagonal_fin_three] at this
      simp only [cons_val, cons_mul, vecMul_cons, head_cons, zero_smul, tail_cons, smul_cons,
                 smul_eq_mul, mul_zero, smul_empty, empty_vecMul, add_zero, zero_add,
                 Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true,
                 true_and] at this
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, of_apply, cons_val]
      · rw [neg_eq_neg_one_mul, ← this.right.left, mul_assoc, not_zero_v101.mul_inv_cancel,
            mul_one]
      · have det_calc: 1 = -((v1 0 1) * (v1 1 0)) * (v1 2 2) := by
          nth_rw 1 [← det_v1, ← second_rep]
          rw [det_fin_three]
          simp only [of_apply, mul_zero, cons_val, zero_mul, zero_sub, add_zero, sub_zero, neg_mul]
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
                simp only [cons_val, mul_one, mul_zero, add_zero, mul_neg, neg_zero, zero_add,
                          neg_neg]
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd1] at this
          simp only [v2]
          nth_rw 2 [← this]
          rfl
        rw [d1, diagonal_fin_three] at this
        nth_rw 10 [← this, eta_fin_three v2]
        simp only [cons_val, cons_mul, vecMul_cons, head_cons, one_smul, tail_cons, zero_smul,
                   empty_vecMul, add_zero, neg_smul, neg_cons, zero_add, empty_mul,
                   Equiv.symm_apply_apply, smul_cons, smul_eq_mul, mul_one, mul_zero, mul_neg,
                   add_cons, empty_add_empty, neg_zero, neg_neg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, of_apply, cons_val]
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
                simp only [cons_val, neg_zero, zero_add, cons_mul, vecMul_cons, head_cons,
                          neg_smul, one_smul, neg_cons, neg_empty, tail_cons, zero_smul, empty_mul]
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd2, hd3] at this
          rw [← SpecialLinearGroup.coe_mul, this]
          rfl
        exact this
      rw [d3, d2, diagonal_fin_three, diagonal_fin_three, ← first_rep] at this
      simp only [cons_val, cons_mul, vecMul_cons, head_cons, smul_cons, smul_eq_mul,
                mul_neg, mul_one, mul_zero, smul_empty, tail_cons, zero_smul, empty_vecMul,
                add_zero, add_cons, zero_add, empty_add_empty, empty_mul, neg_smul, one_smul,
                neg_cons, neg_zero, neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj,
                and_true, true_and] at this
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, of_apply, cons_val]
      · exact (zero_iff_eq_neg_self _).mpr this.left.symm
      · exact (zero_iff_eq_neg_self _).mpr this.right
    have det_v2: det v2 = 1 := by
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v212: IsUnit (v2 1 2) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, det_fin_three] at det_v2
      simp only [of_apply, cons_val', mul_zero, cons_val, zero_mul, sub_self, add_zero,
                 zero_ne_one] at det_v2
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
              simp only [cons_val, mul_zero, mul_neg, mul_one, zero_add, add_zero, neg_zero]
            apply Subtype.ext this
          rw [this]
        rw [map_mul, map_mul, hd1] at this
        simp only [v2]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      rw [← second_rep, d1, diagonal_fin_three] at this
      simp only [cons_val, cons_mul, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_zero,
                smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul,
                Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true,
                true_and] at this
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, of_apply, cons_val]
      · have det_calc: 1 = - (v2 0 0) * (v2 1 2) * (v2 2 1) := by
          nth_rw 1 [← det_v2, ← second_rep]
          rw [det_fin_three]
          simp only [of_apply, mul_zero, cons_val, zero_mul, zero_sub, add_zero, sub_zero, neg_mul]
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
      simp only [cons_val, cons_mul, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_one,
                mul_zero, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
                mul_neg, empty_mul, Equiv.symm_apply_apply, neg_smul, neg_cons, neg_zero,
                neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, neg_inj, true_and]
      exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩,
    by
      congr
      rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
          mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], diag_preserved.right.left, d2,
          diagonal_fin_three]
      simp only [cons_val, cons_mul, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_one,
                mul_zero, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
                mul_neg, empty_mul, Equiv.symm_apply_apply, neg_smul, neg_cons, neg_zero,
                neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, neg_inj, true_and]
      exact ⟨ l1unit.inv_mul_cancel, l2unit.mul_inv_cancel ⟩,
    by
      congr
      rw [← mul_assoc, mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
          mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], diag_preserved.right.right, d3,
          diagonal_fin_three]
      simp only [cons_val, cons_mul, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_one,
                mul_zero, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
                mul_neg, empty_mul, Equiv.symm_apply_apply, neg_smul, neg_cons, neg_zero,
                neg_empty, EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, neg_inj, true_and]
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


def x12 : Matrix (Fin 3) (Fin 3) (R) :=
    !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def x12SL : SL3 R :=
  ⟨x12 R, by
    simp [x12, Matrix.det_fin_three]
  ⟩



def graphChoiceSL3 (ε : Bool) : AutSL3 R :=
  if ε then invTransposeAutSL3 R else (1 : AutSL3 R)


theorem x12_preserved (φ : AutSL3 (F)) : ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (x12SL F))) = x12SL F := by
  sorry


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
