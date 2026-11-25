import StandardClebschAtLabel
import FiniteTensorCoefficient

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem standardClebschAtLabel_first_mismatch (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L)
    (k:Fin (L+1)) (z:Fin (m+1)) (hz:z.val≠r.val+k.val) :
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
      (standardClebschAtLabel q hq hq1 l m r L hL (standardWeightBasis L k)) (0,z)=0 := by
  subst L
  dsimp only [standardClebschAtLabel]
  rw [← standardClebschCoefficient_eq_repr]
  apply standardClebschCoefficient_weight_mismatch
  simp only [Fin.val_zero,Nat.cast_zero,zero_add]
  exact_mod_cast hz

theorem standardClebschAtLabel_first_closed (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L)
    (k:Fin (L+1)) (z:Fin (m+1)) (hz:z.val=r.val+k.val) :
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
      (standardClebschAtLabel q hq hq1 l m r L hL (standardWeightBasis L k)) (0,z)=
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹*q^(-(k.val:ℤ)*(l:ℤ))*
        qfactorial q (m-r.val)*qfactorial q (L-k.val)/
          (qfactorial q L*qfactorial q (m-z.val)) := by
  subst L
  dsimp only [standardClebschAtLabel]
  rw [← standardClebschCoefficient_eq_repr]
  exact standardClebschCoefficient_first_closed q hq hq1 l m r k z.val hz (by have hh:=z.isLt;omega)

theorem standardClebschAtLabel_first_highest (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L) (z:Fin (m+1)) (hz:z.val=r.val) :
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
      (standardClebschAtLabel q hq hq1 l m r L hL (standardWeightBasis L 0)) (0,z)=
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹ := by
  rw [standardClebschAtLabel_first_closed q hq hq1 l m r L hL 0 z (by simpa using hz)]
  simp only [Fin.val_zero,Nat.cast_zero,neg_zero,zero_mul,zpow_zero,mul_one,Nat.sub_zero,hz]
  field_simp [qfactorial_ne_zero q hq L,qfactorial_ne_zero q hq (m-r.val)]

/-- The source boundary coordinate is exactly supported in z >= r. -/
theorem standardClebschAtLabel_first_below (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (L:ℕ) (hL:coupledLabel l m r=L)
    (k:Fin (L+1)) (z:Fin (m+1)) (hz:z.val<r.val) :
    ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).repr
      (standardClebschAtLabel q hq hq1 l m r L hL (standardWeightBasis L k)) (0,z)=0 :=
  standardClebschAtLabel_first_mismatch q hq hq1 l m r L hL k z (by omega)

end AMSPhysical
#print axioms AMSPhysical.standardClebschAtLabel_first_closed
#print axioms AMSPhysical.standardClebschAtLabel_first_below
