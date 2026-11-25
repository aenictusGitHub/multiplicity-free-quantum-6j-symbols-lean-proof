import StandardClebschFirstCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def standardClebschShiftIndex (h a b:ℕ) (r:Fin (min a b+1)):Fin (min (a+h) (b+h)+1):=
  ⟨r.val+h,by have hr:=r.isLt;omega⟩
def standardWeightShiftIndex (h b:ℕ) (k:Fin (b+1)):Fin (b+h+1):=
  ⟨k.val+h,by have hk:=k.isLt;omega⟩

theorem standardClebschShift_label (h a b:ℕ) (r:Fin (min a b+1)):
    coupledLabel (a+h) (b+h) (standardClebschShiftIndex h a b r)=coupledLabel a b r := by
  change a+h+(b+h)-2*(r.val+h)=a+b-2*r.val
  omega

/-- Exact first-coordinate determinant-background transformation of the
independently constructed standard Clebsch map, with its actual norm. -/
theorem standardClebsch_first_determinant_shift (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b:ℕ) (r:Fin (min a b+1)) (L:ℕ) (hL:coupledLabel a b r=L)
    (k:Fin (L+1)) (z:Fin (b+1)) (hz:z.val=r.val+k.val) :
    ((standardWeightBasis (K:=ℝ) (a+h)).tensorProduct (standardWeightBasis (K:=ℝ) (b+h))).repr
      (standardClebschAtLabel q hq hq1 (a+h) (b+h) (standardClebschShiftIndex h a b r) L
        ((standardClebschShift_label h a b r).trans hL) (standardWeightBasis L k))
      (0,standardWeightShiftIndex h b z)=
    (Real.sqrt (quantumHighestNorm q a b r)/
      Real.sqrt (quantumHighestNorm q (a+h) (b+h) (standardClebschShiftIndex h a b r)))*
      q^(-(h:ℤ)*(k.val:ℤ))*
      ((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b)).repr
        (standardClebschAtLabel q hq hq1 a b r L hL (standardWeightBasis L k)) (0,z) := by
  rw [standardClebschAtLabel_first_closed q hq hq1 (a+h) (b+h) (standardClebschShiftIndex h a b r) L
    ((standardClebschShift_label h a b r).trans hL) k (standardWeightShiftIndex h b z) (by
      change z.val+h=(r.val+h)+k.val
      omega),standardClebschAtLabel_first_closed q hq hq1 a b r L hL k z hz]
  simp only [standardClebschShiftIndex,standardWeightShiftIndex,Fin.val_mk,Nat.add_sub_add_right]
  have hp:q^(-(k.val:ℤ)*((a+h:ℕ):ℤ))=q^(-(h:ℤ)*(k.val:ℤ))*q^(-(k.val:ℤ)*(a:ℤ)):=by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  rw [hp]
  have hN:Real.sqrt (quantumHighestNorm q a b r)≠0:=ne_of_gt (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq a b r))
  field_simp [hN,qfactorial_ne_zero q hq L,qfactorial_ne_zero q hq (b-z.val)]

end AMSPhysical
#print axioms AMSPhysical.standardClebsch_first_determinant_shift
