import PolynomialAdjointGram

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open MvPolynomial
variable {σ τ : Type*} [DecidableEq σ] [Fintype τ] [DecidableEq τ]

theorem fock_one_one : fock (1 : MvPolynomial τ ℂ) 1=1 := by
  change fock (monomial 0 1 : MvPolynomial τ ℂ) (monomial 0 1)=1
  rw [fock_monomials,if_pos rfl]
  simp [monomialWeight]

/-- Build the abstract induction interface from actual ambient polynomial
maps, literal creation multipliers and actual Fock-adjoint annihilators. -/
def fockPolynomialAdjointForm
    (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ)
    (F : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (M : σ → MvPolynomial τ ℂ) (L : σ → MvPolynomial τ ℂ → MvPolynomial τ ℂ)
    (hCreation : ∀ i p,F (X i*p)=M i*F p)
    (hAnnihilation : ∀ i p,L i (F p)=F (D i p))
    (hAdjoint : ∀ i p q,fock (M i*p) q=fock p (L i q)) :
    PolynomialAdjointForm D where
  pair p q := fock (F p) (F q)
  add_left p q r := by rw [map_add,fock_add_left]
  add_right p q r := by rw [map_add,fock_add_right]
  smul_left a p q := by rw [map_smul,fock_smul_left]
  smul_right a p q := by rw [map_smul,fock_smul_right]
  adj_left i p q := by rw [hCreation,hAdjoint,hAnnihilation]
  adj_right i p q := by
    calc
      fock (F p) (F (X i*q))=star (fock (F (X i*q)) (F p)) := (fock_conj_symm _ _).symm
      _=star (fock (F q) (F (D i p))) := by rw [hCreation,hAdjoint,hAnnihilation]
      _=fock (F (D i p)) (F q) := fock_conj_symm _ _

end AMSPhysical
