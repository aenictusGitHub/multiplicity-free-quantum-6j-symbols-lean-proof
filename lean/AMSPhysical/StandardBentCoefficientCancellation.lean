import StandardClebschFirstCoordinate
import QuantumFactorials

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Exact cancellation of the physical cup weight against the source
Clebsch coefficient. The result is the independent complementary highest
coupling coefficient, including its phase. -/
theorem standardBent_source_coefficient (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ)
    (r:Fin (min d c+1)) (L:ℕ) (hL:coupledLabel d c r=L)
    (t:Fin (L+1)) (z:Fin (c+1)) (hz:z.val=r.val+t.val) :
    ((-1:ℝ)^(z.val:ℤ))*
      ((standardWeightBasis (K:=ℝ) d).tensorProduct (standardWeightBasis (K:=ℝ) c)).repr
        (standardClebschAtLabel q hq hq1 d c r L hL (standardWeightBasis L t)) (0,z)/quantumWeight q L t.val=
      ((-1:ℝ)^(r.val:ℤ))/(Real.sqrt (quantumHighestNorm q d c r))*
        couplingCoefficient q (c:ℤ) (c-r.val) t.val := by
  have hrd:=channel_left_bound d c r
  have hrc:=channel_right_bound d c r
  have ht:t.val≤c-r.val:=by have hzc:=z.isLt;omega
  have htL:t.val≤L:=by have hh:=t.isLt;omega
  have hci:(c-r.val:ℕ)=c-z.val+t.val:=by omega
  have hLi:(L:ℤ)=(d:ℤ)+(c:ℤ)-2*(r.val:ℤ):=by unfold coupledLabel at hL;omega
  have hPow:q^(-(t.val:ℤ)*(d:ℤ))=
      q^(couplingExponent (c:ℤ) (c-r.val) t.val)*q^(quantumWeightExponent L t.val):=by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    unfold couplingExponent quantumWeightExponent
    have hcr:((c-r.val:ℕ):ℤ)=(c:ℤ)-(r.val:ℤ):=by omega
    rw [hcr,hLi]
    ring
  have hSign:(-1:ℝ)^(z.val:ℤ)=(-1:ℝ)^(r.val:ℤ)*(-1:ℝ)^t.val:=by
    rw [show (z.val:ℤ)=(r.val:ℤ)+(t.val:ℤ) from by omega,zpow_add₀ (by norm_num),zpow_natCast]
    simp only [zpow_natCast]
  rw [standardClebschAtLabel_first_closed q hq hq1 d c r L hL t z hz,
    couplingCoefficient_factorial q hq hq1 (c:ℤ) (c-r.val) t.val ht]
  unfold quantumWeight
  rw [hPow,hSign,show c-r.val-t.val=c-z.val from by omega]
  have hf(k:ℕ):qfactorial q k≠0:=qfactorial_ne_zero q hq k
  field_simp [hf,zpow_ne_zero (quantumWeightExponent L t.val) (ne_of_gt hq)]

end AMSPhysical
#print axioms AMSPhysical.standardBent_source_coefficient
