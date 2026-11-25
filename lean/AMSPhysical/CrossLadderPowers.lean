import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem quantumTransfer_creation_power (R T : Module.End ℝ V) (Q : ℝ)
    (hTR : ∀ v,T (R v)=Q • R (T v)) (t : ℕ) (f : V) :
    T ((R^t) f)=Q^t • (R^t) (T f) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hP (v : V) : (R^(t+1)) v=R ((R^t) v) := DFunLike.congr_fun (pow_succ' R t) v
    rw [hP,hTR,ih,map_smul,smul_smul,hP,pow_succ]
    congr 1
    ring

/-- An off-pair contraction can be pushed through arbitrarily many cups
using only its exact transfer commutator. -/
theorem quantumCrossLadder_power (A R T : Module.End ℝ V) (Q : ℝ) (g : ℕ → ℝ)
    (hg0 : g 0=0) (hg : ∀ t,g (t+1)=g t+Q^t)
    (hAR : ∀ v,A (R v)=R (A v)+T v) (hTR : ∀ v,T (R v)=Q • R (T v))
    (t : ℕ) (f : V) :
    A ((R^(t+1)) f)=(R^(t+1)) (A f)+g (t+1) • (R^t) (T f) := by
  induction t with
  | zero => simpa only [pow_zero,pow_one,Module.End.one_apply,hg 0,hg0,zero_add,one_smul] using hAR f
  | succ t ih =>
    have hP (v : V) : (R^((t+1)+1)) v=R ((R^(t+1)) v) := DFunLike.congr_fun (pow_succ' R (t+1)) v
    have hP' (v : V) : (R^(t+1)) v=R ((R^t) v) := DFunLike.congr_fun (pow_succ' R t) v
    rw [hP,hAR,ih,map_add,map_smul,quantumTransfer_creation_power R T Q hTR,
      ← hP,← hP',add_assoc,← add_smul,← hg (t+1)]

end AMSPhysical
