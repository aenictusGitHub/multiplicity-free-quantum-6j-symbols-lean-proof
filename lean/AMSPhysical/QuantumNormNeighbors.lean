import QuantumNormRatios
import QuantumCoupledStrings

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem couplingNormClosed_outer_neighbor (q : ℝ) (hq : 0<q) (l m r k : ℕ)
    (hl : r≤l) (hm : r≤m) (hkr : k+1=r) :
    couplingNormClosed q (l-r) (m-r) r*
      (qnum q (l-r+1)*qnum q (m-r+1)*qnum q (l+m-r+2))=
      q^(4*(r:ℤ)-2*(m:ℤ)-2)*qnum q r*qnum q (coupledLabel l m r+2)*qnum q (coupledLabel l m r+3)*
        couplingNormClosed q (l-k) (m-k) k := by
  have h := couplingNormClosed_outer_step q hq (l-r) (m-r) k
  have h₁ : (l-r)+(m-r)+k+3=l+m-r+2 := by omega
  have h₂ : (l-r)+(m-r)=coupledLabel l m r := by unfold coupledLabel;omega
  have h₃ : (l-r)+1=l-k := by omega
  have h₄ : (m-r)+1=m-k := by omega
  have hphase : 2*(k:ℤ)-2*((m-r:ℕ):ℤ)=4*(r:ℤ)-2*(m:ℤ)-2 := by omega
  rw [h₁,h₂,hphase,hkr] at h
  simpa only [h₃,h₄] using h

theorem couplingNormClosed_root_neighbor (q : ℝ) (hq : 0<q) (i n s : ℕ)
    (hi : s≤ i) (hn : s<n) :
    couplingNormClosed q (i+2-(s+1)) (n-(s+1)) (s+1)*
      (qnum q (n-s)*qnum q (i+1)*qnum q (i+2))=
      q^(4*(s:ℤ)+2-2*(n:ℤ))*qnum q (s+1)*qnum q (i-s+1)*qnum q (i+n-s+2)*
        couplingNormClosed q (i-s) (n-s) s := by
  have h := couplingNormClosed_root_step q hq (i-s) (n-s-1) s
  have h₁ : (n-s-1)+1=n-s := by omega
  have h₂ : (i-s)+s+1=i+1 := by omega
  have h₃ : (i-s)+s+2=i+2 := by omega
  have h₄ : (i-s)+(n-s-1)+s+3=i+n-s+2 := by omega
  have h₅ : (i-s)+1=i+2-(s+1) := by omega
  have h₆ : n-s-1=n-(s+1) := by omega
  have hphase : 2*(s:ℤ)-2*((n-s-1:ℕ):ℤ)=4*(s:ℤ)+2-2*(n:ℤ) := by omega
  rw [h₁,h₂,h₃,h₄,hphase] at h
  simpa only [h₅,h₆] using h

end AMSPhysical

#print axioms AMSPhysical.couplingNormClosed_outer_neighbor
#print axioms AMSPhysical.couplingNormClosed_root_neighbor
