import FockOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open MvPolynomial

def determinantVacuum (vectorSide : Bool) : P8 ℂ := if vectorSide then detX else detY

def determinantAnnihilator (vectorSide : Bool) (p : P8 ℂ) : P8 ℂ :=
  if vectorSide then pderiv 3 (pderiv 0 p)-pderiv 2 (pderiv 1 p)
  else pderiv 7 (pderiv 4 p)-pderiv 6 (pderiv 5 p)

theorem determinantVacuum_adjoint (vectorSide : Bool) (p q : P8 ℂ) :
    fock (determinantVacuum vectorSide*p) q=fock p (determinantAnnihilator vectorSide q) := by
  cases vectorSide <;>
    simp only [determinantVacuum,determinantAnnihilator,Bool.false_eq_true,if_false,if_true,
      detX,detY,sub_mul,fock_sub_left,fock_sub_right,mul_assoc,
      fock_mulX_pderiv]

/-- The 2-by-2 Cayley differential identity on the literal determinant. -/
theorem determinantAnnihilator_power (vectorSide : Bool) (h : ℕ) :
    determinantAnnihilator vectorSide (determinantVacuum vectorSide^(h+1))=
      (((h+1)*(h+2):ℕ):ℂ) • determinantVacuum vectorSide^h := by
  cases h with
  | zero =>
    cases vectorSide <;>
      simp [determinantVacuum,determinantAnnihilator,detX,detY,pderiv_pow,Algebra.smul_def,map_ofNat]
    all_goals ring
  | succ h =>
    cases vectorSide <;>
      simp [determinantVacuum,determinantAnnihilator,detX,detY,pderiv_pow,
        Nat.succ_eq_add_one,show h+1+1-1=h+1 by omega,Algebra.smul_def]
    all_goals simp only [pow_succ,map_ofNat]
    all_goals ring

theorem determinantVacuum_fock_norm_succ (vectorSide : Bool) (h : ℕ) :
    fock (determinantVacuum vectorSide^(h+1)) (determinantVacuum vectorSide^(h+1))=
      (((h+1)*(h+2):ℕ):ℂ)*fock (determinantVacuum vectorSide^h) (determinantVacuum vectorSide^h) := by
  conv_lhs => lhs;rw [pow_succ,mul_comm]
  rw [determinantVacuum_adjoint,determinantAnnihilator_power,fock_smul_right]

/-- Exact label-independent normalization, derived from actual polynomial
derivatives and actual factorial Fock pairing, not supplied as a norm axiom. -/
theorem determinantVacuum_fock_norm (vectorSide : Bool) (h : ℕ) :
    fock (determinantVacuum vectorSide^h) (determinantVacuum vectorSide^h)=
      ((h.factorial*(h+1).factorial:ℕ):ℂ) := by
  induction h with
  | zero =>
    simp only [pow_zero]
    rw [show (1 : P8 ℂ)=monomial 0 1 by rfl,fock_monomials,if_pos rfl]
    simp [monomialWeight]
  | succ h ih =>
    rw [determinantVacuum_fock_norm_succ,ih]
    simp only [Nat.factorial_succ,Nat.succ_eq_add_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

end AMSPhysical
#print axioms AMSPhysical.determinantVacuum_fock_norm
