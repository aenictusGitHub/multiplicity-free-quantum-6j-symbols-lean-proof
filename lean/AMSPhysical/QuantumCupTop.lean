import QuantumCupIndexSteps

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupTop (l m c : ℕ) (hadm : m ≤ l+c) : QuantumCupIndex l m c :=
  ⟨⟨min l m,by omega⟩,⟨by change min l m ≤ l;omega,by change m-min l m ≤ c;omega⟩⟩

theorem quantumCupTop_max (l m c : ℕ) (hadm : m ≤ l+c) (r : QuantumCupIndex l m c) :
    r.val.val ≤ (quantumCupTop l m c hadm).val.val := by
  change r.val.val ≤ min l m
  have hl:=r.property.1
  have ht:=r.val.isLt
  omega

theorem quantumCup_notTop_canRaiseLeft (l m c : ℕ) (hadm : m ≤ l+c) (r : QuantumCupIndex l m c)
    (hr : r≠quantumCupTop l m c hadm) : quantumCupCanRaiseLeft l m c r := by
  have hne : r.val.val≠min l m := by
    intro he
    apply hr
    apply Subtype.ext
    exact Fin.ext he
  have hm:=quantumCupTop_max l m c hadm r
  change r.val.val ≤ min l m at hm
  constructor <;> omega

theorem quantumCup_raisedLeft_canRaiseRight (l m c : ℕ) (r : QuantumCupIndex l m c)
    (hr : quantumCupCanRaiseLeft l m c r) :
    quantumCupCanRaiseRight l m c (quantumCupRaiseLeft l m c r hr) := by
  change 0 < r.val.val+1 ∧ m-(r.val.val+1)+1 ≤ c
  have hm:=hr.2
  have hc:=r.property.2
  constructor <;> omega

theorem quantumCup_raiseRight_raiseLeft (l m c : ℕ) (r : QuantumCupIndex l m c)
    (hr : quantumCupCanRaiseLeft l m c r) :
    quantumCupRaiseRight l m c (quantumCupRaiseLeft l m c r hr) (quantumCup_raisedLeft_canRaiseRight l m c r hr)=r := by
  apply Subtype.ext
  apply Fin.ext
  change (r.val.val+1)-1=r.val.val
  omega

theorem quantumCupRightOffDiagonal_nonzero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ)
    (l m h c : ℕ) (r : QuantumCupIndex l m c) (hr : quantumCupCanRaiseRight l m c r) :
    quantumCupLeftOffDiagonal q n (c:ℤ) (h:ℤ) (l:ℤ) (m-r.val.val) r.val.val≠0 := by
  unfold quantumCupLeftOffDiagonal
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (ne_of_gt hq))
    · apply ne_of_gt
      apply qInteger_pos_real q hq hq1
      have hc:=hr.2
      omega
  · apply ne_of_gt
    apply qInteger_pos_real q hq hq1
    have ht:=hr.1
    omega

end AMSPhysical
