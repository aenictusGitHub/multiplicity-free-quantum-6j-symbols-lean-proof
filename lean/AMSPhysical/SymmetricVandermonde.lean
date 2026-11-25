import QuantumFactorials

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical

def symmetricMultiset (q : ℝ) (a r : ℕ) : ℝ :=
  qfactorial q (a+r)/(qfactorial q a*qfactorial q r)

theorem gaussianFactorial_symmetric (q : ℝ) (a r : ℕ) :
    gaussianFactorial q a r=q^((a*r:ℕ):ℤ)*symmetricMultiset q a r := by
  unfold gaussianFactorial symmetricMultiset
  ring

theorem symmetricVandermonde_summand (q : ℝ) (hq : 0<q) (a b r i j : ℕ) (hij : i+j=r) :
    q^(-(((a+2*b+2)*r:ℕ):ℤ)) *
      (gaussianFactorial q b i*((q^2)^(b+1))^j*gaussianFactorial q a j)=
      q^(-((i*(a+b+2):ℕ):ℤ))*symmetricMultiset q a j*symmetricMultiset q b i := by
  rw [gaussianFactorial_symmetric,gaussianFactorial_symmetric]
  have hp : ((q^2)^(b+1))^j=q^((2*(b+1)*j:ℕ):ℤ) := by rw [zpow_natCast,pow_mul,pow_mul]
  rw [hp]
  have he : -(((a+2*b+2)*r:ℕ):ℤ)+((b*i:ℕ):ℤ)+((2*(b+1)*j:ℕ):ℤ)+((a*j:ℕ):ℤ)=
      -((i*(a+b+2):ℕ):ℤ) := by
    have hs : (i:ℤ)+(j:ℤ)=(r:ℤ) := by exact_mod_cast hij
    push_cast
    rw [← hs]
    ring
  calc
    _=(q^(-(((a+2*b+2)*r:ℕ):ℤ))*q^((b*i:ℕ):ℤ)*q^((2*(b+1)*j:ℕ):ℤ)*q^((a*j:ℕ):ℤ))*
        (symmetricMultiset q a j*symmetricMultiset q b i) := by ring
    _=q^(-(((a+2*b+2)*r:ℕ):ℤ)+((b*i:ℕ):ℤ)+((2*(b+1)*j:ℕ):ℤ)+((a*j:ℕ):ℤ))*
        (symmetricMultiset q a j*symmetricMultiset q b i) := by
      rw [zpow_add₀ (ne_of_gt hq),zpow_add₀ (ne_of_gt hq),zpow_add₀ (ne_of_gt hq)]
    _=_ := by rw [he];ring

/-- The negative-power symmetric quantum Vandermonde identity used by the actual coupling norm. -/
theorem symmetric_vandermonde (q : ℝ) (hq : 0<q) (a b r : ℕ) :
    (∑ ij∈Finset.antidiagonal r,q^(-((ij.1*(a+b+2):ℕ):ℤ))*
      symmetricMultiset q a ij.2*symmetricMultiset q b ij.1)=
      q^(-((r*(b+1):ℕ):ℤ))*symmetricMultiset q (a+b+1) r := by
  have h := congrArg (fun x : ℝ => q^(-(((a+2*b+2)*r:ℕ):ℤ))*x)
    (gaussianFactorial_vandermonde q hq a b r)
  dsimp only at h
  rw [Finset.mul_sum] at h
  have hs : (∑ ij∈Finset.antidiagonal r,q^(-(((a+2*b+2)*r:ℕ):ℤ))*
      (gaussianFactorial q b ij.1*((q^2)^(b+1))^ij.2*gaussianFactorial q a ij.2))=
      ∑ ij∈Finset.antidiagonal r,q^(-((ij.1*(a+b+2):ℕ):ℤ))*
        symmetricMultiset q a ij.2*symmetricMultiset q b ij.1 := by
    apply Finset.sum_congr rfl
    intro ij hij
    exact symmetricVandermonde_summand q hq a b r ij.1 ij.2 (Finset.mem_antidiagonal.mp hij)
  rw [hs] at h
  rw [← h,gaussianFactorial_symmetric,← mul_assoc,← zpow_add₀ (ne_of_gt hq)]
  congr 2
  push_cast
  ring

end AMSPhysical

#print axioms AMSPhysical.symmetric_vandermonde
