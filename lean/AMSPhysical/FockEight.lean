import FockOperators
import Reduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]

def polynomialPair (x y : ι → σ) : MvPolynomial σ ℂ := ∑ i,X (x i)*X (y i)
def polynomialLap (x y : ι → σ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ i,pderiv (y i) (pderiv (x i) p)
def polynomialColor (x y : ι → σ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ i,X (x i)*pderiv (y i) p

theorem polynomialPair_lap_adjoint (x y : ι → σ) (p q : MvPolynomial σ ℂ) :
    fock (polynomialPair x y*p) q=fock p (polynomialLap x y q) := by
  simp only [polynomialPair,polynomialLap,Finset.sum_mul,fock_sum_left,fock_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,fock_mulX_pderiv,fock_mulX_pderiv]

theorem polynomialPair_lap_selfadjoint (x y : ι → σ) :
    IsFockSelfAdjoint (fun p => polynomialPair x y*polynomialLap x y p) := by
  intro p q
  change fock (polynomialPair x y*polynomialLap x y p) q=
    fock p (polynomialPair x y*polynomialLap x y q)
  calc
    fock (polynomialPair x y*polynomialLap x y p) q=
      fock (polynomialLap x y p) (polynomialLap x y q) := polynomialPair_lap_adjoint x y _ _
    _=star (fock (polynomialLap x y q) (polynomialLap x y p)) := (fock_conj_symm _ _).symm
    _=star (fock (polynomialPair x y*polynomialLap x y q) p) := by rw [polynomialPair_lap_adjoint]
    _=fock p (polynomialPair x y*polynomialLap x y q) := fock_conj_symm p _

theorem polynomialColor_adjoint (x y : ι → σ) :
    IsFockAdjoint (polynomialColor x y) (polynomialColor y x) := by
  intro p q
  simp only [polynomialColor,fock_sum_left,fock_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fock_mulX_pderiv,fock_pderiv_mulX]

theorem mixedXYAmbient_fock_selfadjoint : IsFockSelfAdjoint (mixedXYAmbient (R:=ℂ)) := by
  have h := polynomialPair_lap_selfadjoint (![0,1] : Fin 2 → Fin 8) (![4,5] : Fin 2 → Fin 8)
  simpa only [polynomialPair,polynomialLap,IsFockSelfAdjoint,IsFockAdjoint,mixedXYAmbient,
    coords,lap,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem mixedZYAmbient_fock_selfadjoint : IsFockSelfAdjoint (mixedZYAmbient (R:=ℂ)) := by
  have h := polynomialPair_lap_selfadjoint (![2,3] : Fin 2 → Fin 8) (![4,5] : Fin 2 → Fin 8)
  simpa [polynomialPair,polynomialLap,IsFockSelfAdjoint,IsFockAdjoint,mixedZYAmbient,
    coords,lap,Fin.sum_univ_two] using h

theorem omegaXX_fock_selfadjoint : IsFockSelfAdjoint (omegaXX (R:=ℂ)) := by
  have hR := polynomialColor_adjoint (![0,1] : Fin 2 → Fin 8) (![2,3] : Fin 2 → Fin 8)
  have hL := polynomialColor_adjoint (![2,3] : Fin 2 → Fin 8) (![0,1] : Fin 2 → Fin 8)
  have hE := polynomialColor_adjoint (![0,1] : Fin 2 → Fin 8) (![0,1] : Fin 2 → Fin 8)
  simp only [IsFockAdjoint,polynomialColor,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hR hL hE
  intro p q
  rw [omegaXX,fock_sub_left,omegaXX,fock_sub_right]
  rw [show fock (raiseColor (lowerColor p)) q=fock (lowerColor p) (lowerColor q) from hR (lowerColor p) q,
    show fock (lowerColor p) (lowerColor q)=fock p (raiseColor (lowerColor q)) from hL p (lowerColor q),
    show fock (eulerX p) q=fock p (eulerX q) from hE p q]

end AMSPhysical

#print axioms AMSPhysical.omegaXX_fock_selfadjoint
