import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 600000
noncomputable section
namespace AMSPhysical
open PowerSeries

def geometricSeries (a : ℝ) : PowerSeries ℝ := rescale a (mk 1)

theorem geometricSeries_coeff (a : ℝ) (n : ℕ) : coeff n (geometricSeries a)=a^n := by
  simp [geometricSeries]

theorem geometricSeries_inverse (a : ℝ) :
    geometricSeries a*(1-C a*X)=1 := by
  have h := congrArg (rescale a) (mk_one_mul_one_sub_eq_one ℝ)
  simpa only [map_mul,map_sub,map_one,rescale_X,geometricSeries] using h

theorem geometricSeries_rescale (a b : ℝ) :
    rescale a (geometricSeries b)=geometricSeries (a*b) := by
  ext n
  simp only [coeff_rescale,geometricSeries_coeff,mul_pow]

def gaussianSeries (Q : ℝ) (a : ℕ) : PowerSeries ℝ :=
  ∏ i∈Finset.range (a+1),geometricSeries (Q^i)

def gaussianCoefficient (Q : ℝ) (a r : ℕ) : ℝ := coeff r (gaussianSeries Q a)

theorem gaussianSeries_zero (Q : ℝ) : gaussianSeries Q 0=geometricSeries 1 := by
  simp [gaussianSeries]

theorem gaussianSeries_succ (Q : ℝ) (a : ℕ) :
    gaussianSeries Q (a+1)=gaussianSeries Q a*geometricSeries (Q^(a+1)) := by
  exact Finset.prod_range_succ (fun i => geometricSeries (Q^i)) (a+1)

theorem gaussianCoefficient_zero_left (Q : ℝ) (r : ℕ) : gaussianCoefficient Q 0 r=1 := by
  simp [gaussianCoefficient,gaussianSeries_zero,geometricSeries_coeff]

theorem gaussianCoefficient_zero_right (Q : ℝ) (a : ℕ) : gaussianCoefficient Q a 0=1 := by
  unfold gaussianCoefficient gaussianSeries
  rw [coeff_zero_eq_constantCoeff_apply,map_prod]
  simp only [← coeff_zero_eq_constantCoeff_apply,geometricSeries_coeff,pow_zero,Finset.prod_const_one]

theorem gaussianSeries_difference (Q : ℝ) (a : ℕ) :
    gaussianSeries Q (a+1)*(1-C (Q^(a+1))*X)=gaussianSeries Q a := by
  rw [gaussianSeries_succ,mul_assoc,geometricSeries_inverse,mul_one]

theorem gaussianCoefficient_step (Q : ℝ) (a r : ℕ) :
    gaussianCoefficient Q (a+1) (r+1)=gaussianCoefficient Q a (r+1)+
      Q^(a+1)*gaussianCoefficient Q (a+1) r := by
  have h := congrArg (coeff (r+1)) (gaussianSeries_difference Q a)
  rw [mul_sub,mul_one,map_sub,← mul_assoc,coeff_succ_mul_X,coeff_mul_C] at h
  unfold gaussianCoefficient
  linarith

theorem gaussianSeries_split (Q : ℝ) (a b : ℕ) :
    gaussianSeries Q (a+b+1)=gaussianSeries Q b*rescale (Q^(b+1)) (gaussianSeries Q a) := by
  unfold gaussianSeries
  rw [map_prod]
  have hlen : a+b+1+1=(b+1)+(a+1) := by omega
  rw [hlen,Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [geometricSeries_rescale,pow_add]

/-- Gaussian Vandermonde convolution, obtained from a literal split of the geometric alphabet. -/
theorem gaussian_vandermonde (Q : ℝ) (a b r : ℕ) :
    gaussianCoefficient Q (a+b+1) r=
      ∑ ij∈Finset.antidiagonal r,
        gaussianCoefficient Q b ij.1 * (Q^(b+1))^ij.2 * gaussianCoefficient Q a ij.2 := by
  unfold gaussianCoefficient
  rw [gaussianSeries_split,coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [coeff_rescale]
  ring

end AMSPhysical

#print axioms AMSPhysical.gaussian_vandermonde
