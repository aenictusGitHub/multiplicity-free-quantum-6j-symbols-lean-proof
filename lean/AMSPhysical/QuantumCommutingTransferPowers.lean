import QuantumGeometricPowers
import CrossLadderPowers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem qGeometricInteger_nat_succ_left (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (t : ℕ) :
    qGeometricInteger q ((t+1:ℕ):ℤ)=q^(-2:ℤ)*qGeometricInteger q (t:ℤ)+1 := by
  rw [Nat.cast_add,Nat.cast_one,add_comm (t:ℤ) 1,qGeometricInteger_add q hq]
  have h1 : qGeometricInteger q 1=1 := by simp only [qGeometricInteger,sub_self,zpow_zero,qInteger_one q hD,mul_one]
  rw [h1]
  ring

theorem commutingTransfer_creation_power (R T : Module.End ℝ V) (hTR : ∀ v,T (R v)=R (T v))
    (t : ℕ) (f : V) : T ((R^t) f)=(R^t) (T f) := by
  have h:=quantumTransfer_creation_power R T 1 (by intro v;simpa only [one_smul] using hTR v) t f
  simpa only [one_pow,one_smul] using h

theorem qCommutator_commutingTransfer_power (A R T : Module.End ℝ V) (Q : ℝ) (g : ℕ → ℝ)
    (hg0 : g 0=0) (hg : ∀ t,g (t+1)=Q*g t+1)
    (hAR : ∀ v,A (R v)=Q • R (A v)+T v) (hTR : ∀ v,T (R v)=R (T v))
    (t : ℕ) (f : V) :
    A ((R^(t+1)) f)=Q^(t+1) • (R^(t+1)) (A f)+g (t+1) • (R^t) (T f) := by
  induction t with
  | zero => simpa only [pow_zero,pow_one,Module.End.one_apply,hg 0,hg0,mul_zero,zero_add,one_smul] using hAR f
  | succ t ih =>
    have hP (v : V) : (R^((t+1)+1)) v=R ((R^(t+1)) v) := DFunLike.congr_fun (pow_succ' R (t+1)) v
    have hP' (v : V) : (R^(t+1)) v=R ((R^t) v) := DFunLike.congr_fun (pow_succ' R t) v
    rw [hP,hAR,ih,map_add,map_smul,map_smul,smul_add,smul_smul,smul_smul,
      commutingTransfer_creation_power R T hTR,← hP,← hP']
    have hQ : Q*Q^(t+1)=Q^((t+1)+1) := by rw [pow_succ];ring
    rw [hQ,hg (t+1),add_smul,one_smul]
    abel

end AMSPhysical
