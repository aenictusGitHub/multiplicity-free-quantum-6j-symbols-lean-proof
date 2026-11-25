import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

/-- Two independently checked channel normalizations fix the positive
four-triangle prefactor exactly, with no free square-root sign. -/
theorem positiveTwoChannelNormalization (D E k L R L' R' I J : ℝ)
    (hD : 0<D) (hE : 0<E) (hk : 0<k) (hL : 0<L) (hR : 0<R)
    (hL' : 0<L') (hR' : 0<R') (hI : 0<I) (hJ : 0<J)
    (hLeft : D*k*L=I*L') (hRight : E*k*R=J*R') :
    Real.sqrt (I*J)*Real.sqrt (L'*R')/Real.sqrt (D*E)=k*Real.sqrt (L*R) := by
  have hm : D*E*k^2*L*R=I*J*L'*R' := by
    calc
      _ = (D*k*L)*(E*k*R) := by ring
      _ = (I*L')*(J*R') := by rw [hLeft,hRight]
      _ = _ := by ring
  have hs : (Real.sqrt (D*E)*(k*Real.sqrt (L*R)))^2=
      (Real.sqrt (I*J)*Real.sqrt (L'*R'))^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_pos hD hE).le,Real.sq_sqrt (mul_pos hL hR).le,
      mul_pow,Real.sq_sqrt (mul_pos hI hJ).le,Real.sq_sqrt (mul_pos hL' hR').le]
    nlinarith [hm]
  have ha : 0≤Real.sqrt (D*E)*(k*Real.sqrt (L*R)) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hk.le (Real.sqrt_nonneg _))
  have hb : 0≤Real.sqrt (I*J)*Real.sqrt (L'*R') := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have he : Real.sqrt (I*J)*Real.sqrt (L'*R')=Real.sqrt (D*E)*(k*Real.sqrt (L*R)) := by nlinarith
  apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (mul_pos hD hE)))).mpr
  rw [he]
  ring

end AMSPhysical
#print axioms AMSPhysical.positiveTwoChannelNormalization
