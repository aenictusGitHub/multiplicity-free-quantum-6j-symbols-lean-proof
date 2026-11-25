import QuantumDimensionProductIdentity

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def quantumOscillatorLadderCoefficient (q : ℝ) (S : ℤ) (t : ℕ) : ℝ :=
  q^(-S-2*(t:ℤ)+2)*qInteger q (t:ℤ)*qInteger q (S+(t:ℤ))

theorem quantumOscillatorLadderCoefficient_zero (q : ℝ) (S : ℤ) :
    quantumOscillatorLadderCoefficient q S 0=0 := by
  simp only [quantumOscillatorLadderCoefficient,Nat.cast_zero,qInteger_zero,mul_zero,zero_mul]

theorem quantumOscillatorLadderCoefficient_succ (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (S : ℤ) (t : ℕ) :
    quantumOscillatorLadderCoefficient q S (t+1)=
      q^(-2:ℤ)*quantumOscillatorLadderCoefficient q S t+
        q^(-S-2*(t:ℤ))*qInteger q (S+2*(t:ℤ)+1) := by
  have h:=qInteger_shift_product q hq (t:ℤ) (S+(t:ℤ)) 1
  rw [qInteger_one q hD,one_mul] at h
  have he : q^(-2:ℤ)*q^(-S-2*(t:ℤ)+2)=q^(-S-2*(t:ℤ)) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  unfold quantumOscillatorLadderCoefficient
  simp only [Nat.cast_add,Nat.cast_one]
  have he' : -S-2*((t:ℤ)+1)+2= -S-2*(t:ℤ) := by ring
  rw [he']
  have h' : qInteger q ((t:ℤ)+1)*qInteger q (S+(t:ℤ)+1)-qInteger q (t:ℤ)*qInteger q (S+(t:ℤ))=
      qInteger q (S+2*(t:ℤ)+1) := by convert h using 1 <;> congr 1 <;> ring
  calc
    _ = q^(-S-2*(t:ℤ))*qInteger q (t:ℤ)*qInteger q (S+(t:ℤ))+
        q^(-S-2*(t:ℤ))*qInteger q (S+2*(t:ℤ)+1) := by
          simp only [← add_assoc]
          linear_combination q^(-S-2*(t:ℤ))*h'
    _ = _ := by rw [← he];ring

end AMSPhysical
