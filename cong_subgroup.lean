import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection

open Matrix


abbrev SL3 (A : Type*) [CommRing A] :=
  Matrix.SpecialLinearGroup (Fin 3) A


namespace CongruenceSubgroup


/-
DO NOT CHANGE
-/
variable (R : Type*) [CommRing R] [IsLocalRing R] [Invertible (2 : R)]


/-- The residue field `k = R / m` of the local ring `R`. -/
abbrev k :=
  IsLocalRing.ResidueField R


abbrev m :=
  IsLocalRing.maximalIdeal R


/-- The reduction map `ρ : SL₃(R) → SL₃(k)`. -/
def ρ : SL3 R →* SL3 (k R) :=
  Matrix.SpecialLinearGroup.map (IsLocalRing.residue R)


/-- The principal congruence subgroup `N = ker ρ`. -/
def N : Subgroup (SL3 R) :=
  MonoidHom.ker (ρ R)

def C : Subgroup (SL3 R) :=
  Subgroup.comap (ρ R) (Subgroup.center (SL3 (k R)))


/-
Have to prove
-/
def transvectionSL3 (i j : Fin 3) (hij : i ≠ j) (c : R) : SL3 R :=
  ⟨Matrix.transvection i j c, by
    exact Matrix.det_transvection_of_ne i j hij c
  ⟩



def TransvectionSetSL3 : Set (SL3 R) :=
  { g | ∃ i j : Fin 3, ∃ hij : i ≠ j, ∃ c : R,
      g = transvectionSL3 R i j hij c }



def E3 : Subgroup (SL3 R) :=
  Subgroup.closure (TransvectionSetSL3 R)



theorem SL3_generated_by_transvections :
    E3 R = (⊤ : Subgroup (SL3 R)) := by
  sorry



theorem C_largest_normal : ∀ (H : Subgroup (SL3 R)), H.Normal ∧ (H ≠ ⊤) →
    H ≤ (C R) := by
    intro H ⟨nH,HneSL3⟩
    sorry



theorem C_characteristic : (C R).Characteristic := by
  sorry



theorem N_comm : (N R) = ⁅(C R),⊤⁆ := by
  sorry



/-
Have to prove
-/
theorem N_characteristic : (N R).Characteristic := by
  sorry


end CongruenceSubgroup
