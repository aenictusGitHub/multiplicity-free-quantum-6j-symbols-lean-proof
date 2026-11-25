import DeterminantLadderTransport
import PolynomialFockForm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open MvPolynomial

def sourcePairingAdjointForm (n : ℕ) : PolynomialAdjointForm (pairingRadial (R:=ℂ) n) :=
  fockPolynomialAdjointForm (pairingRadial n) (pullN (R:=ℂ) n).toLinearMap (coordsN n)
    (fun i =>lapN n (pairingVectorSlot i) (pairingCovectorSlot i))
    (by intro i p;simp [pullN,map_mul])
    (pairingRadial_actual n)
    (by
      intro i p q
      have hc : coordsN (R:=ℂ) n i=dotN n (pairingVectorSlot i) (pairingCovectorSlot i) := by
        fin_cases i <;> rfl
      rw [hc]
      exact fock_contraction_lap n _ _ p q)

def determinantPairingAdjointForm (vectorSide : Bool) (h : ℕ) :
    PolynomialAdjointForm (pairingRadial (R:=ℂ) (2+h)) :=
  fockPolynomialAdjointForm (pairingRadial (2+h)) (determinantPairingEval vectorSide h)
    coords pairingLaplacian8 (determinantPairingEval_creation vectorSide h)
    (determinantPairingEval_annihilation vectorSide h) pairingLaplacian8_adjoint

/-- The exact universal normalization from the simplified proof, for all
pairing polynomials, every rank, both determinant orientations, and ALL labels.
It is derived from actual Fock adjunction, not from an assumed overlap formula. -/
theorem universalDeterminant_fock_normalization (vectorSide : Bool) (h : ℕ) (f g : P4 ℂ) :
    fock (determinantVacuum vectorSide^h*pull f) (determinantVacuum vectorSide^h*pull g)=
      ((h.factorial*(h+1).factorial:ℕ):ℂ)*fock (pullN (2+h) f) (pullN (2+h) g) := by
  apply PolynomialAdjointForm.unique_scale (pairingRadial (2+h)) (pairingRadial_one (2+h))
    (sourcePairingAdjointForm (2+h)) (determinantPairingAdjointForm vectorSide h)
  change fock (determinantVacuum vectorSide^h*pull 1) (determinantVacuum vectorSide^h*pull 1)=
    ((h.factorial*(h+1).factorial:ℕ):ℂ)*fock (pullN (2+h) 1) (pullN (2+h) 1)
  rw [map_one,mul_one,map_one,fock_one_one,mul_one]
  exact determinantVacuum_fock_norm vectorSide h

theorem shiftI_fock_universal (h : ℕ) (f g : P4 ℂ) :
    fock (shiftI h f) (shiftI h g)=
      ((h.factorial*(h+1).factorial:ℕ):ℂ)*fock (pullN (2+h) f) (pullN (2+h) g) :=
  universalDeterminant_fock_normalization false h f g

theorem shiftII_fock_universal (h : ℕ) (f g : P4 ℂ) :
    fock (shiftII h f) (shiftII h g)=
      ((h.factorial*(h+1).factorial:ℕ):ℂ)*fock (pullN (2+h) f) (pullN (2+h) g) :=
  universalDeterminant_fock_normalization true h f g

end AMSPhysical
#print axioms AMSPhysical.universalDeterminant_fock_normalization
