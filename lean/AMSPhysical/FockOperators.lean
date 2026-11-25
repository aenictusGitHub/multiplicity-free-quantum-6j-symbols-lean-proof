import Fock
import Radial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def IsFockAdjoint (A B : MvPolynomial σ ℂ → MvPolynomial σ ℂ) : Prop :=
  ∀ p q, fock (A p) q=fock p (B q)

def IsFockSelfAdjoint (A : MvPolynomial σ ℂ → MvPolynomial σ ℂ) : Prop :=
  IsFockAdjoint A A

theorem fock_adjoint_comp (A B C D : MvPolynomial σ ℂ → MvPolynomial σ ℂ)
    (hAB : IsFockAdjoint A B) (hCD : IsFockAdjoint C D) :
    IsFockAdjoint (A ∘ C) (D ∘ B) := by
  intro p q
  exact (hAB (C p) q).trans (hCD p (B q))

theorem fock_adjoint_symm (A B : MvPolynomial σ ℂ → MvPolynomial σ ℂ)
    (h : IsFockAdjoint A B) : IsFockAdjoint B A := by
  intro p q
  calc
    fock (B p) q=star (fock q (B p)) := (fock_conj_symm (B p) q).symm
    _=star (fock (A q) p) := by rw [h q p]
    _=fock p (A q) := fock_conj_symm p (A q)

theorem fock_sub_left (p q r : MvPolynomial σ ℂ) :
    fock (p-q) r=fock p r-fock q r := by
  rw [sub_eq_add_neg,fock_add_left,← neg_one_smul ℂ q,fock_smul_left]
  simp [sub_eq_add_neg]

theorem fock_sub_right (p q r : MvPolynomial σ ℂ) :
    fock p (q-r)=fock p q-fock p r := by
  rw [sub_eq_add_neg,fock_add_right,← neg_one_smul ℂ r,fock_smul_right]
  simp [sub_eq_add_neg]

theorem fock_contraction_lap (n : ℕ) (v w : Fin 4) (p q : PN ℂ n) :
    fock (dotN n v w*p) q=fock p (lapN n v w q) := by
  simp only [dotN,lapN,Finset.sum_mul,fock_sum_left,fock_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,fock_mulX_pderiv,fock_mulX_pderiv]

/-- Q Delta is selfadjoint in the genuine polynomial Fock pairing. -/
theorem mixed_pair_fock_selfadjoint (n : ℕ) (v w : Fin 4) :
    IsFockSelfAdjoint (fun p : PN ℂ n => dotN n v w*lapN n v w p) := by
  intro p q
  change fock (dotN n v w*lapN n v w p) q=fock p (dotN n v w*lapN n v w q)
  calc
    fock (dotN n v w*lapN n v w p) q=fock (lapN n v w p) (lapN n v w q) :=
      fock_contraction_lap n v w _ _
    _=star (fock (lapN n v w q) (lapN n v w p)) := (fock_conj_symm _ _).symm
    _=star (fock (dotN n v w*lapN n v w q) p) := by rw [fock_contraction_lap]
    _=fock p (dotN n v w*lapN n v w q) := fock_conj_symm _ _

def colorN {R : Type*} [CommRing R] (n : ℕ) (v w : Fin 4) (p : PN R n) : PN R n :=
  ∑ i, X (v,i)*pderiv (w,i) p

theorem colorN_adjoint (n : ℕ) (v w : Fin 4) :
    IsFockAdjoint (colorN n v w) (colorN n w v) := by
  intro p q
  simp only [colorN,fock_sum_left,fock_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fock_mulX_pderiv,fock_pderiv_mulX]

theorem same_pair_fock_selfadjoint (n : ℕ) (v w : Fin 4) :
    IsFockSelfAdjoint (fun p : PN ℂ n =>
      colorN n v w (colorN n w v p)-colorN n v v p) := by
  intro p q
  rw [fock_sub_left,fock_sub_right]
  rw [colorN_adjoint n v w,colorN_adjoint n w v,colorN_adjoint n v v]

def mixedCasimir (n : ℕ) (v w : Fin 4) (a b : ℕ) (p : PN ℂ n) : PN ℂ n :=
  -dotN n v w*lapN n v w p+(((a*b:ℕ):ℂ)/(n:ℂ)) • p

theorem mixedCasimir_fock_selfadjoint (n : ℕ) (v w : Fin 4) (a b : ℕ) :
    IsFockSelfAdjoint (mixedCasimir n v w a b) := by
  intro p q
  have hc : star (((a*b:ℕ):ℂ)/(n:ℂ))=((a*b:ℕ):ℂ)/(n:ℂ) := by simp
  simp only [mixedCasimir,neg_mul,← neg_one_smul ℂ (dotN n v w*lapN n v w p),
    ← neg_one_smul ℂ (dotN n v w*lapN n v w q),fock_add_left,fock_add_right,
    fock_smul_left,fock_smul_right,hc]
  rw [mixed_pair_fock_selfadjoint n v w]
  simp

end AMSPhysical

#print axioms AMSPhysical.mixed_pair_fock_selfadjoint
#print axioms AMSPhysical.same_pair_fock_selfadjoint
#print axioms AMSPhysical.mixedCasimir_fock_selfadjoint
