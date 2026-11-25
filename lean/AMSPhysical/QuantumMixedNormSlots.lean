import QuantumMixedGenerating
import OccupationPowerSeriesGeneral

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def mixedNormSlot (q : ℝ) (a b n : ℕ) (k : Fin (n+1)) : PowerSeries ℝ :=
  if k=0 then PowerSeries.C (qfactorial q a)*gaussianSeries (q^2) a
  else if k=Fin.last n then PowerSeries.C (qfactorial q b)*
    PowerSeries.rescale ((q^2)^(-((n+b:ℕ):ℤ))) (gaussianSeries (q^2) b)
  else geometricSeries ((q^2)^(-(k.val:ℤ)))

theorem square_zpow_natPower (q : ℝ) (s : ℤ) (k : ℕ) : ((q^2)^s)^k=q^(2*s*(k:ℤ)) := by
  rw [← zpow_natCast ((q^2)^s) k,← zpow_mul,← zpow_natCast q 2,← zpow_mul]
  congr 1
  ring

theorem mixedNormSlot_first_coeff (q : ℝ) (hq : 0<q) (a b n k : ℕ) :
    PowerSeries.coeff k (mixedNormSlot q a b n 0)=
      q^((a:ℤ)*(k:ℤ))*qfactorial q (a+k)/qfactorial q k := by
  simp only [mixedNormSlot,if_pos rfl,ite_true,PowerSeries.coeff_C_mul]
  change qfactorial q a*gaussianCoefficient (q^2) a k=_
  rw [gaussianCoefficient_factorial q hq]
  unfold gaussianFactorial
  have he : (((a*k:ℕ):ℤ))=(a:ℤ)*(k:ℤ) := by push_cast;rfl
  rw [he]
  field_simp [qfactorial_ne_zero q hq a,qfactorial_ne_zero q hq k]

theorem mixedNormSlot_last_coeff (q : ℝ) (hq : 0<q) (a b n k : ℕ) (hn : 0<n) :
    PowerSeries.coeff k (mixedNormSlot q a b n (Fin.last n))=
      q^((-2*(n:ℤ)-b)*(k:ℤ))*qfactorial q (b+k)/qfactorial q k := by
  have hlast : (Fin.last n : Fin (n+1))≠0 := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_last,Fin.val_zero] at hh
    omega
  simp only [mixedNormSlot,if_neg hlast,if_pos rfl,ite_true,PowerSeries.coeff_C_mul,PowerSeries.coeff_rescale]
  change qfactorial q b*((((q^2)^(-((n+b:ℕ):ℤ)))^k)*gaussianCoefficient (q^2) b k)=_
  rw [gaussianCoefficient_factorial q hq]
  unfold gaussianFactorial
  have hp : (((q^2)^(-((n+b:ℕ):ℤ)))^k)*q^((b*k:ℕ):ℤ)=q^((-2*(n:ℤ)-b)*(k:ℤ)) := by
    rw [square_zpow_natPower,← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  have he : qfactorial q b*((((q^2)^(-((n+b:ℕ):ℤ)))^k)*
      (q^((b*k:ℕ):ℤ)*qfactorial q (b+k)/(qfactorial q b*qfactorial q k)))=
      ((((q^2)^(-((n+b:ℕ):ℤ)))^k)*q^((b*k:ℕ):ℤ))*qfactorial q (b+k)/qfactorial q k := by
    field_simp [qfactorial_ne_zero q hq b,qfactorial_ne_zero q hq k]
  rw [he,hp]

theorem mixedNormSlot_interior_coeff (q : ℝ) (a b n k : ℕ) (j : Fin (n+1))
    (hj0 : j≠0) (hjn : j≠Fin.last n) :
    PowerSeries.coeff k (mixedNormSlot q a b n j)=q^((-2*(j.val:ℤ))*(k:ℤ)) := by
  rw [mixedNormSlot,if_neg hj0,if_neg hjn,geometricSeries_coeff,square_zpow_natPower]
  congr 1
  ring

end AMSPhysical
#print axioms AMSPhysical.mixedNormSlot_last_coeff
