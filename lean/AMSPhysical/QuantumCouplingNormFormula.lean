import SymmetricVandermonde

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def couplingNormConstant (q : ℝ) (a b r : ℕ) : ℝ :=
  q^((r:ℤ)*(1-(b:ℤ)))*(qfactorial q r)^2*qfactorial q a*qfactorial q b/
    (qfactorial q (a+r)*qfactorial q (b+r))

def couplingNormClosed (q : ℝ) (a b r : ℕ) : ℝ :=
  q^(-2*(r:ℤ)*(b:ℤ))*qfactorial q r*qfactorial q a*qfactorial q b*qfactorial q (a+b+r+1)/
    (qfactorial q (a+r)*qfactorial q (b+r)*qfactorial q (a+b+1))

theorem couplingNorm_summand (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a b r i j : ℕ) (hij : i+j=r) :
    (couplingCoefficient q ((b+r:ℕ):ℤ) r i)^2*quantumWeight q (a+r) i*quantumWeight q (b+r) j=
      couplingNormConstant q a b r*(q^(-((i*(a+b+2):ℕ):ℤ))*
        symmetricMultiset q a j*symmetricMultiset q b i) := by
  have hi : i≤r := by omega
  have hrsub : r-i=j := by omega
  have ha : a+r-i=a+j := by omega
  have hb : b+r-j=b+i := by omega
  have hs : ((-1:ℝ)^i)^2=1 := by
    rw [← pow_mul,mul_comm i 2,pow_mul]
    norm_num
  have hp : (q^(couplingExponent ((b+r:ℕ):ℤ) r i))^2 *
      q^(quantumWeightExponent (a+r) i)*q^(quantumWeightExponent (b+r) j)=
      q^((r:ℤ)*(1-(b:ℤ)))*q^(-((i*(a+b+2):ℕ):ℤ)) := by
    rw [sq,← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq),
      ← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    have he : (i:ℤ)+(j:ℤ)=(r:ℤ) := by exact_mod_cast hij
    simp only [couplingExponent,quantumWeightExponent,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    rw [← he]
    ring
  rw [couplingCoefficient_factorial q hq hq1 _ r i hi,hrsub]
  unfold quantumWeight couplingNormConstant symmetricMultiset
  rw [ha,hb]
  rw [div_pow,mul_pow,mul_pow,hs,one_mul]
  field_simp [qfactorial_ne_zero q hq i,qfactorial_ne_zero q hq j,
    qfactorial_ne_zero q hq a,qfactorial_ne_zero q hq b,
    qfactorial_ne_zero q hq (a+r),qfactorial_ne_zero q hq (b+r)]
  linear_combination
    ((qfactorial q r)^2*qfactorial q (a+j)*qfactorial q (b+i))*hp

/-- The finite norm sum of the actual highest-weight coefficients has a closed factorial form. -/
theorem couplingNorm_sum (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a b r : ℕ) :
    (∑ ij∈Finset.antidiagonal r,(couplingCoefficient q ((b+r:ℕ):ℤ) r ij.1)^2*
      quantumWeight q (a+r) ij.1*quantumWeight q (b+r) ij.2)=couplingNormClosed q a b r := by
  have he : (∑ ij∈Finset.antidiagonal r,(couplingCoefficient q ((b+r:ℕ):ℤ) r ij.1)^2*
      quantumWeight q (a+r) ij.1*quantumWeight q (b+r) ij.2)=
      couplingNormConstant q a b r*(∑ ij∈Finset.antidiagonal r,q^(-((ij.1*(a+b+2):ℕ):ℤ))*
        symmetricMultiset q a ij.2*symmetricMultiset q b ij.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    exact couplingNorm_summand q hq hq1 a b r ij.1 ij.2 (Finset.mem_antidiagonal.mp hij)
  rw [he,symmetric_vandermonde q hq]
  unfold couplingNormConstant symmetricMultiset couplingNormClosed
  have hpow : q^((r:ℤ)*(1-(b:ℤ)))*q^(-((r*(b+1):ℕ):ℤ))=q^(-2*(r:ℤ)*(b:ℤ)) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  have hlen : a+b+1+r=a+b+r+1 := by omega
  rw [hlen]
  field_simp [qfactorial_ne_zero q hq a,qfactorial_ne_zero q hq b,
    qfactorial_ne_zero q hq r,qfactorial_ne_zero q hq (a+r),qfactorial_ne_zero q hq (b+r),
    qfactorial_ne_zero q hq (a+b+1)]
  linear_combination
    qfactorial q (a+b+r+1)*hpow

end AMSPhysical

#print axioms AMSPhysical.couplingNorm_sum
