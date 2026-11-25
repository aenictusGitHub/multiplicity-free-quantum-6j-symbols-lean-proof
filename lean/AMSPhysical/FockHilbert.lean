import Fock
import Mathlib.Analysis.InnerProductSpace.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- An actual positive-definite inner product core for the polynomial Fock space. -/
def fockCore : InnerProductSpace.Core ℂ (MvPolynomial σ ℂ) where
  inner := fock
  conj_inner_symm := fock_conj_symm
  re_inner_nonneg := fock_nonneg
  add_left := fock_add_left
  smul_left p q c := fock_smul_left c p q
  definite := fock_definite

/-- The Fock norm is constructed from the positive-definite factorial pairing. -/
def fockNormedAddCommGroup : NormedAddCommGroup (MvPolynomial σ ℂ) := by
  letI : InnerProductSpace.Core ℂ (MvPolynomial σ ℂ) := fockCore
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

def fockInnerProductSpace :
    letI := @fockNormedAddCommGroup σ _ _
    InnerProductSpace ℂ (MvPolynomial σ ℂ) := by
  letI := @fockNormedAddCommGroup σ _ _
  exact InnerProductSpace.ofCore (fockCore : InnerProductSpace.Core ℂ (MvPolynomial σ ℂ))

end AMSPhysical

#print axioms AMSPhysical.fockCore
#print axioms AMSPhysical.fockInnerProductSpace
