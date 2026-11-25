import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A graded oscillator commutator determines every creation power without
dividing by a ladder coefficient, so vanishing boundary terms are included. -/
theorem gradedOscillator_power (R L : Module.End ℝ V) (Q : ℝ) (a c : ℕ → ℝ)
    (ha0 : a 0=0) (ha : ∀ t,a (t+1)=Q*a t+c t) (f : V)
    (hcomm : ∀ t,L ((R^(t+1)) f)=Q • R (L ((R^t) f))+c t • (R^t) f)
    (t : ℕ) :
    L ((R^(t+1)) f)=Q^(t+1) • (R^(t+1)) (L f)+a (t+1) • (R^t) f := by
  induction t with
  | zero => simpa only [pow_zero,Module.End.one_apply,pow_one,ha 0,ha0,mul_zero,zero_add] using hcomm 0
  | succ t ih =>
    rw [hcomm (t+1),ih,map_add,map_smul,map_smul,smul_add,smul_smul,smul_smul]
    have hpow : R ((R^(t+1)) (L f))=(R^((t+1)+1)) (L f) := by
      exact (DFunLike.congr_fun (pow_succ' R (t+1)) (L f)).symm
    have hpow' : R ((R^t) f)=(R^(t+1)) f := (DFunLike.congr_fun (pow_succ' R t) f).symm
    rw [hpow,hpow',add_assoc,← add_smul,← ha (t+1)]
    have hQ : Q*Q^(t+1)=Q^((t+1)+1) := by rw [pow_succ];ring
    rw [hQ]

end AMSPhysical
