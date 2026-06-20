import Final_Project.cong_subgroup
import Final_Project.field_aut
import Final_Project.local_aut
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

set_option warningAsError false


open Matrix BigOperators CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-
Part 2 of the project.

This file assembles Part 1, Part 3, and Part 4:

* Part 1 gives the characteristic subgroup
  `CongruenceSubgroup.N R = ker (SL₃(R) → SL₃(k))`.
* Part 3 gives the standard classification over the residue field.
* Part 4 gives the normalized local-ring theorem.

The final statement is that every automorphism of `SL₃(R)` is standard.
-/
namespace ResidueReduction

variable (R : Type*) [CommRing R] [IsLocalRing R] [Invertible (2 : R)]

/-- The residue field used in Part 2. -/
abbrev k : Type _ :=
  CongruenceSubgroup.k R

/-- The reduction map `SL₃(R) → SL₃(k)`. -/
abbrev reduction : SL3 R →* SL3 (k R) :=
  CongruenceSubgroup.ρ R

/-- The kernel of the reduction map. -/
abbrev reductionKernel : Subgroup (SL3 R) :=
  CongruenceSubgroup.N R

/-- The quotient by the congruence subgroup. -/
abbrev QuotSL3 : Type _ :=
  SL3 R ⧸ reductionKernel R

/-- The kernel of the reduction map is normal. -/
instance reductionKernelNormal : (reductionKernel R).Normal := by
  dsimp [reductionKernel, CongruenceSubgroup.N]
  infer_instance

/-- Since `2` is invertible in `R`, it is also invertible in the residue field. -/
noncomputable instance residueInvertibleTwo : Invertible (2 : k R) := by
  classical
  sorry

/-- Part 1 output, restated in the notation of this file. -/
theorem reductionKernel_characteristic :
    (reductionKernel R).Characteristic := by
  exact CongruenceSubgroup.N_characteristic R


/--
Step 2.1: an automorphism of `SL₃(R)` descends to the quotient by `N`, because
`N` is characteristic.
-/
def inducedQuotientAut (φ : AutSL3 R) :
    QuotSL3 R ≃* QuotSL3 R := by
  classical
  -- Construct with `QuotientGroup.map` applied to `φ` and `φ.symm`.
  -- The containment hypotheses are exactly `reductionKernel_characteristic R`.
  sorry

/--
Step 2.2: identify `SL₃(R)/N` with `SL₃(k)`.

Mathematically this is the first isomorphism theorem for the reduction map,
using surjectivity of reduction, which follows from elementary generation.
-/
def quotientResidueEquiv :
    QuotSL3 R ≃* SL3 (k R) := by
  classical
  sorry

/--
The induced automorphism on the residue field `k = R / J`.
-/
def inducedResidueAut (φ : AutSL3 R) : AutSL3 (k R) := by
  classical
  -- Transport the quotient automorphism across `quotientResidueEquiv`.
  sorry

/-- The defining commutative square for the induced residue-field automorphism. -/
theorem inducedResidueAut_commutes
    (φ : AutSL3 R) (x : SL3 R) :
    inducedResidueAut R φ ((reduction R) x) =
      (reduction R) (φ x) := by
  sorry

/--
A `GL₃(R)` matrix reduces to a prescribed `GL₃(k)` matrix entrywise.
-/
def GL3ReducesTo (g : GL3 R) (B : GL3 (k R)) : Prop :=
  ∀ i j : Fin 3,
    IsLocalRing.residue R ((g : Matrix (Fin 3) (Fin 3) R) i j) =
      (B : Matrix (Fin 3) (Fin 3) (k R)) i j

/--
Step 2.3: lift the field-level conjugating matrix from `GL₃(k)` to `GL₃(R)`.
This uses locality: if the determinant is nonzero modulo `J`, its lift is a unit.
-/
def liftGL3FromResidue (B : GL3 (k R)) : GL3 R := by
  classical
  sorry

/-- The chosen lift really reduces to the prescribed matrix over the residue field. -/
theorem liftGL3FromResidue_spec (B : GL3 (k R)) :
    GL3ReducesTo R (liftGL3FromResidue R B) B := by
  sorry

/--
The normalized automorphism used in Block 2.

Mathematically:
`Ψ = Γ_R^ε ∘ i_{\tilde B}^{-1} ∘ φ`, where `\tilde B` is a lift of the
field-level conjugating matrix `B`.
-/
def normalizeByResidueStandardData
    (φ : AutSL3 R)
    (B : GL3 (k R))
    (σk : k R ≃+* k R)
    (ε : Bool) : AutSL3 R := by
  classical
  sorry

/--
After field-level normalization, the new automorphism fixes the six standard
matrices modulo the maximal ideal.
-/
theorem normalizeByResidueStandardData_fixed_mod
    (φ : AutSL3 R)
    (B : GL3 (k R))
    (σk : k R ≃+* k R)
    (ε : Bool)
    (hfield :
      ∀ x : SL3 (k R),
        inducedResidueAut R φ x =
          ringAutSL3 (k R) σk
            ((FieldAutomorpisms.graphChoiceSL3 (k R) ε)
              (innerAutSL3byGL3 (k R) B x))) :
    LocalAutomorphisms.BasicGeneratorsFixedModJ R
      (normalizeByResidueStandardData R φ B σk ε) := by
  sorry

/--
Undoing the Block 2 normalization preserves standardness.  This is the final
bookkeeping step: multiply back the lifted inner automorphism and, if necessary,
the graph automorphism.
-/
theorem standard_of_normalized
    (φ : AutSL3 R)
    (B : GL3 (k R))
    (σk : k R ≃+* k R)
    (ε : Bool)
    (hstd :
      LocalAutomorphisms.IsStandardSL3Aut R
        (normalizeByResidueStandardData R φ B σk ε)) :
    LocalAutomorphisms.IsStandardSL3Aut R φ := by
  sorry


/--
Part 2 final assembly: every automorphism of `SL₃(R)` is standard.
-/
theorem every_aut_SL3_standard
    (φ : AutSL3 R) :
    LocalAutomorphisms.IsStandardSL3Aut R φ := by
  sorry

end ResidueReduction

end
