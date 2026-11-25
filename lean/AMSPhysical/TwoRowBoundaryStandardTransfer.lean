import TwoRowBoundaryClebschAction
import StandardPairTransfer

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def standardPairTransferAtTotal (q:ℝ) (hq:0<q) (hq1:q≠1) (S r l m l' m':ℕ)
    (hS:l+m=S) (hS':l'+m'=S) (hl:r≤l) (hm:r≤m) (hl':r≤l') (hm':r≤m') :=
  standardPairTransfer q hq hq1 l m ⟨r,by omega⟩ l' m' ⟨r,by omega⟩ (S-2*r)
    (by change l+m-2*r=S-2*r;omega) (by change l'+m'-2*r=S-2*r;omega)

theorem standardPairTransferAtTotal_selected (q:ℝ) (hq:0<q) (hq1:q≠1) (S r l m l' m':ℕ)
    (hS:l+m=S) (hS':l'+m'=S) (hl:r≤l) (hm:r≤m) (hl':r≤l') (hm':r≤m')
    (v:finiteWeightSpace (K:=ℝ) (S-2*r)) :
    standardPairTransferAtTotal q hq hq1 S r l m l' m' hS hS' hl hm hl' hm'
      (standardClebschAtTotal q hq hq1 S r l m hS hl hm v)=
      standardClebschAtTotal q hq hq1 S r l' m' hS' hl' hm' v :=
  standardPairTransfer_selected q hq hq1 l m ⟨r,by omega⟩ l' m' ⟨r,by omega⟩ (S-2*r) _ _ v

theorem standardPairTransferAtTotal_other (q:ℝ) (hq:0<q) (hq1:q≠1) (S l m l' m':ℕ)
    (hS:l+m=S) (hS':l'+m'=S) (r s:TwoRowFusionIndex l m) (hrs:r≠s)
    (hl':r.val≤l') (hm':r.val≤m') (v:finiteWeightSpace (K:=ℝ) (coupledLabel l m s)) :
    standardPairTransferAtTotal q hq hq1 S r.val l m l' m' hS hS'
      (channel_left_bound l m r) (channel_right_bound l m r) hl' hm'
      (unitaryQuantumClebschMap q hq hq1 l m s v)=0 :=
  standardPairTransfer_other q hq hq1 l m r s hrs l' m' ⟨r.val,by omega⟩ (S-2*r.val) _ _ v

/-- Literal equality of the entire independently constructed physical pair
boundary map with the independent standard Clebsch partial isometry. -/
theorem twoRowBoundaryPairMap_eq_standard (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (S r l m l' m':ℕ) (hS:l+m=S) (hS':l'+m'=S)
    (hl:r≤l) (hm:r≤m) (hl':r≤l') (hm':r≤m') :
    twoRowBoundaryPairMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm'=
      standardPairTransferAtTotal q hq hq1 S r l m l' m' hS hS' hl hm hl' hm' := by
  subst S
  apply (quantumOrthonormalCoupledBasis q hq hq1 l m).ext
  rintro ⟨s,k⟩
  rw [quantumOrthonormalCoupledBasis_apply]
  dsimp only [orthonormalCoupledVector]
  by_cases hr:r=s.val
  · subst r
    change twoRowBoundaryPairMap q hq hq1 n hn (l+m) s.val l m l' m' rfl hS' hl hm hl' hm'
        (standardClebschAtTotal q hq hq1 (l+m) s.val l m rfl hl hm
          (orthonormalWeightVector q (coupledLabel l m s) k))=
      standardPairTransferAtTotal q hq hq1 (l+m) s.val l m l' m' rfl hS' hl hm hl' hm'
        (standardClebschAtTotal q hq hq1 (l+m) s.val l m rfl hl hm
          (orthonormalWeightVector q (coupledLabel l m s) k))
    rw [twoRowBoundaryPairMap_selected,standardPairTransferAtTotal_selected]
  · let r':TwoRowFusionIndex l m:=⟨r,by omega⟩
    have hrs:r'≠s:=by intro he;apply hr;exact congrArg Fin.val he
    rw [twoRowBoundaryPairMap_other q hq hq1 n hn (l+m) l m l' m' rfl hS' r' s hrs hl' hm',
      standardPairTransferAtTotal_other q hq hq1 (l+m) l m l' m' rfl hS' r' s hrs hl' hm']

end AMSPhysical
#print axioms AMSPhysical.twoRowBoundaryPairMap_eq_standard
