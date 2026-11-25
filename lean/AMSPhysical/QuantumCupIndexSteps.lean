import QuantumCupIndependent
import QuantumCupRankShiftCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupCanRaiseLeft (l m c : ℕ) (r : QuantumCupIndex l m c) : Prop :=
  r.val.val+1 ≤ l ∧ r.val.val < m

instance quantumCupCanRaiseLeftDecidable (l m c : ℕ) (r : QuantumCupIndex l m c) :
    Decidable (quantumCupCanRaiseLeft l m c r) := inferInstanceAs (Decidable (r.val.val+1 ≤ l ∧ r.val.val < m))

def quantumCupRaiseLeft (l m c : ℕ) (r : QuantumCupIndex l m c) (hr : quantumCupCanRaiseLeft l m c r) : QuantumCupIndex l m c :=
  ⟨⟨r.val.val+1,by have ht:=hr.2;omega⟩,⟨hr.1,by change m-(r.val.val+1) ≤ c;have hc:=r.property.2;have ht:=hr.2;omega⟩⟩

def quantumCupCanRaiseRight (l m c : ℕ) (r : QuantumCupIndex l m c) : Prop :=
  0 < r.val.val ∧ m-r.val.val+1 ≤ c

instance quantumCupCanRaiseRightDecidable (l m c : ℕ) (r : QuantumCupIndex l m c) :
    Decidable (quantumCupCanRaiseRight l m c r) := inferInstanceAs (Decidable (0 < r.val.val ∧ m-r.val.val+1 ≤ c))

def quantumCupRaiseRight (l m c : ℕ) (r : QuantumCupIndex l m c) (hr : quantumCupCanRaiseRight l m c r) : QuantumCupIndex l m c :=
  ⟨⟨r.val.val-1,by have ht:=r.val.isLt;omega⟩,⟨by change r.val.val-1 ≤ l;have hl:=r.property.1;omega,
    by change m-(r.val.val-1) ≤ c;have hc:=hr.2;have ht:=hr.1;have hu:=r.val.isLt;omega⟩⟩

theorem quantumCupRaiseLeft_rightCount (l m c : ℕ) (r : QuantumCupIndex l m c)
    (hr : quantumCupCanRaiseLeft l m c r) :
    m-(quantumCupRaiseLeft l m c r hr).val.val=(m-r.val.val)-1 := by
  change m-(r.val.val+1)=(m-r.val.val)-1
  omega

theorem quantumCupRaiseRight_rightCount (l m c : ℕ) (r : QuantumCupIndex l m c)
    (hr : quantumCupCanRaiseRight l m c r) :
    m-(quantumCupRaiseRight l m c r hr).val.val=(m-r.val.val)+1 := by
  change m-(r.val.val-1)=(m-r.val.val)+1
  have ht:=hr.1
  have hu:=r.val.isLt
  omega

theorem quantumCupLeftOffDiagonal_boundary_zero (q : ℝ) (n : ℕ) (l m c : ℕ) (h : ℤ)
    (r : QuantumCupIndex l m c) (hr : ¬ quantumCupCanRaiseLeft l m c r) :
    quantumCupLeftOffDiagonal q n (l:ℤ) h (c:ℤ) r.val.val (m-r.val.val)=0 := by
  by_cases ht : r.val.val < m
  · have he : r.val.val=l := by have hl:=r.property.1;unfold quantumCupCanRaiseLeft at hr;omega
    unfold quantumCupLeftOffDiagonal
    rw [he,sub_self,qInteger_zero,mul_zero,zero_mul]
  · have he : m-r.val.val=0 := by omega
    simp only [quantumCupLeftOffDiagonal,he,Nat.cast_zero,qInteger_zero,mul_zero]

theorem quantumCupRightOffDiagonal_boundary_zero (q : ℝ) (n : ℕ) (l m c : ℕ) (h : ℤ)
    (r : QuantumCupIndex l m c) (hr : ¬ quantumCupCanRaiseRight l m c r) :
    quantumCupLeftOffDiagonal q n (c:ℤ) h (l:ℤ) (m-r.val.val) r.val.val=0 := by
  by_cases ht : 0 < r.val.val
  · have he : m-r.val.val=c := by have hc:=r.property.2;unfold quantumCupCanRaiseRight at hr;omega
    unfold quantumCupLeftOffDiagonal
    rw [he,sub_self,qInteger_zero,mul_zero,zero_mul]
  · have he : r.val.val=0 := by omega
    simp only [quantumCupLeftOffDiagonal,he,Nat.cast_zero,qInteger_zero,mul_zero]

end AMSPhysical
