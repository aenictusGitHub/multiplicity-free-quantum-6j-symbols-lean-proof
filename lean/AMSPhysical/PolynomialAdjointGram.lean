import Fock

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open MvPolynomial
variable {σ : Type*} [DecidableEq σ]

/-- A polynomial sesquilinear pairing with independently supplied adjoint
annihilators. No irreducibility, positivity or physical identification is assumed. -/
structure PolynomialAdjointForm (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ) where
  pair : MvPolynomial σ ℂ → MvPolynomial σ ℂ → ℂ
  add_left : ∀ p q r,pair (p+q) r=pair p r+pair q r
  add_right : ∀ p q r,pair p (q+r)=pair p q+pair p r
  smul_left : ∀ a p q,pair (a • p) q=star a*pair p q
  smul_right : ∀ a p q,pair p (a • q)=a*pair p q
  adj_left : ∀ i p q,pair (X i*p) q=pair p (D i q)
  adj_right : ∀ i p q,pair p (X i*q)=pair (D i p) q

theorem PolynomialAdjointForm.zero_left
    (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ) (B : PolynomialAdjointForm D)
    (p : MvPolynomial σ ℂ) : B.pair 0 p=0 := by
  simpa only [zero_smul,star_zero,zero_mul] using B.smul_left 0 0 p

theorem PolynomialAdjointForm.zero_right
    (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ) (B : PolynomialAdjointForm D)
    (p : MvPolynomial σ ℂ) : B.pair p 0=0 := by
  simpa only [zero_smul,zero_mul] using B.smul_right 0 p 0

/-- Moving a creation to the vacuum gives zero; the only surviving term
is the literal constant coefficient. -/
theorem PolynomialAdjointForm.vacuum
    (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ) (hD : ∀ i,D i 1=0)
    (B : PolynomialAdjointForm D) (p : MvPolynomial σ ℂ) :
    B.pair 1 p=constantCoeff p*B.pair 1 1 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    conv_lhs => rw [C_eq_smul_one,B.smul_right]
    rw [constantCoeff_C]
  | add p q hp hq => simp only [B.add_right,hp,hq,map_add,add_mul]
  | mul_X p i hp =>
    rw [mul_comm p (X i),B.adj_right,hD,B.zero_left]
    simp

/-- The creation/annihilation adjunctions and one vacuum norm determine
EVERY polynomial Gram coefficient by structural polynomial induction. -/
theorem PolynomialAdjointForm.unique
    (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ) (hD : ∀ i,D i 1=0)
    (B C : PolynomialAdjointForm D) (hNorm : B.pair 1 1=C.pair 1 1)
    (p q : MvPolynomial σ ℂ) : B.pair p q=C.pair p q := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C a =>
    rw [show MvPolynomial.C a=a • (1 : MvPolynomial σ ℂ) from C_eq_smul_one,
      B.smul_left,C.smul_left,B.vacuum D hD,C.vacuum D hD,hNorm]
  | add p r hp hr => rw [B.add_left,C.add_left,hp,hr]
  | mul_X p i hp => rw [mul_comm p (X i),B.adj_left,C.adj_left,hp]

def PolynomialAdjointForm.scale
    (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ) (B : PolynomialAdjointForm D) (c : ℂ) :
    PolynomialAdjointForm D where
  pair p q := c*B.pair p q
  add_left p q r := by rw [B.add_left,mul_add]
  add_right p q r := by rw [B.add_right,mul_add]
  smul_left a p q := by rw [B.smul_left];ring
  smul_right a p q := by rw [B.smul_right];ring
  adj_left i p q := congrArg (c*·) (B.adj_left i p q)
  adj_right i p q := congrArg (c*·) (B.adj_right i p q)

theorem PolynomialAdjointForm.unique_scale
    (D : σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ) (hD : ∀ i,D i 1=0)
    (B C : PolynomialAdjointForm D) (c : ℂ) (hNorm : C.pair 1 1=c*B.pair 1 1)
    (p q : MvPolynomial σ ℂ) : C.pair p q=c*B.pair p q :=
  PolynomialAdjointForm.unique D hD C (B.scale D c) hNorm p q

end AMSPhysical
#print axioms AMSPhysical.PolynomialAdjointForm.unique_scale
