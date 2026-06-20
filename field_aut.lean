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
    !![0, -1, 0;
     1, 0, 0;
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
  sorry



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


def IsTransvectionSL3 (x : SL3 F) : Prop :=
  ∃ i j : Fin 3, ∃ c : F,
    i ≠ j ∧
    (x : Matrix (Fin 3) (Fin 3) F) =
      Matrix.transvection i j c


theorem field_class
    (φ : AutSL3 F) :
    ∃ (σ : F ≃+* F) (ε : Bool) (g : GL (Fin 3) F),
      ∀ (x : SL3 F),
        φ x =
            ringAutSL3 F σ ((graphChoiceSL3 F ε) (innerAutSL3byGL3 F g x))
             := by
  sorry

end FieldAutomorpisms
