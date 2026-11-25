import GaussianSeries
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def geometricBlock (Q : ℝ) (s : ℤ) (L : ℕ) : PowerSeries ℝ :=
  ∏ k∈Finset.range L,geometricSeries (Q^(s+(k:ℤ)))

theorem geometricBlock_concat (Q : ℝ) (s : ℤ) (u v : ℕ) :
    geometricBlock Q s (u+v)=geometricBlock Q s u*geometricBlock Q (s+(u:ℤ)) v := by
  unfold geometricBlock
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  congr 2
  push_cast
  ring

theorem geometricBlock_gaussian (Q : ℝ) (hQ : Q≠0) (s : ℤ) (a : ℕ) :
    geometricBlock Q s (a+1)=PowerSeries.rescale (Q^s) (gaussianSeries Q a) := by
  unfold geometricBlock gaussianSeries
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [geometricSeries_rescale,zpow_add₀ hQ,zpow_natCast]

theorem geometricBlock_zero (Q : ℝ) (a : ℕ) : geometricBlock Q 0 (a+1)=gaussianSeries Q a := by
  simp only [geometricBlock,gaussianSeries,zero_add,zpow_natCast]

theorem geometricBlock_negative (Q : ℝ) (m : ℕ) :
    (∏ k∈Finset.range m,geometricSeries (Q^(-((k+1:ℕ):ℤ))))=geometricBlock Q (-(m:ℤ)) m := by
  rw [← Finset.prod_range_reflect (fun k : ℕ => geometricSeries (Q^(-((k+1:ℕ):ℤ)))) m]
  unfold geometricBlock
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  congr 2
  omega

/-- The exact consecutive geometric alphabet behind the arbitrary-rank mixed
highest-vector norm; the empty interior at rank one is included. -/
theorem gaussian_mixed_alphabet (Q : ℝ) (hQ : Q≠0) (a b n : ℕ) (hn : 0<n) :
    gaussianSeries Q a*
      (∏ k∈Finset.range (n-1),geometricSeries (Q^(-((k+1:ℕ):ℤ))))*
      PowerSeries.rescale (Q^(-((n+b:ℕ):ℤ))) (gaussianSeries Q b)=
      PowerSeries.rescale (Q^(-((n+b:ℕ):ℤ))) (gaussianSeries Q (a+n+b)) := by
  rw [geometricBlock_negative,← geometricBlock_zero Q a,← geometricBlock_gaussian Q hQ _ b]
  have hs : -((n+b:ℕ):ℤ)+((b+1:ℕ):ℤ)= -((n-1:ℕ):ℤ) := by omega
  have hlen : b+1+(n-1)=n+b := by omega
  have hs' : -((n+b:ℕ):ℤ)+((n+b:ℕ):ℤ)=0 := by ring
  calc
    _ = (geometricBlock Q (-((n+b:ℕ):ℤ)) (b+1)*
        geometricBlock Q (-((n-1:ℕ):ℤ)) (n-1))*geometricBlock Q 0 (a+1) := by ring
    _ = geometricBlock Q (-((n+b:ℕ):ℤ)) (n+b)*
        geometricBlock Q (-((n+b:ℕ):ℤ)+((n+b:ℕ):ℤ)) (a+1) := by
      rw [← hs,← geometricBlock_concat,hlen,hs']
    _ = geometricBlock Q (-((n+b:ℕ):ℤ)) (a+n+b+1) := by
      rw [← geometricBlock_concat]
      congr 1
      omega
    _ = _ := geometricBlock_gaussian Q hQ _ _

end AMSPhysical
#print axioms AMSPhysical.gaussian_mixed_alphabet
