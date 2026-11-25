import QuantumHighestNorm
import QuantumClebschAnalytic
import QuantumOccupationUnitWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- Swapping the contraction and the second residual degree gives a simple
quantum-dimension ratio in the exact actual Clebsch norm. -/
theorem couplingNormClosed_bent (q:ℝ) (hq:0<q) (p x r:ℕ):
    couplingNormClosed q p r x=
      (qnum q (p+x+1)/qnum q (p+r+1))*couplingNormClosed q p x r := by
  have he:q^(-2*(x:ℤ)*(r:ℤ))=q^(-2*(r:ℤ)*(x:ℤ)):=by congr 1;ring
  unfold couplingNormClosed
  rw [he]
  simp only [show p+r+x+1=p+x+r+1 from by omega,
    show r+x=x+r from by omega,qfactorial_succ]
  have hf(k:ℕ):qfactorial q k≠0:=qfactorial_ne_zero q hq k
  have hi:qnum q (p+r+1)≠0:=ne_of_gt (qnum_pos q hq (p+r+1) (by omega))
  have hj:qnum q (p+x+1)≠0:=ne_of_gt (qnum_pos q hq (p+x+1) (by omega))
  field_simp [hf,hi,hj]

theorem quantumHighestNorm_bent (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ)
    (r:Fin (min d c+1)) (L:ℕ) (hL:coupledLabel d c r=L)
    (u:Fin (min L c+1)) (hu:u.val=c-r.val):
    quantumHighestNorm q L c u=
      (qInteger q ((L+1:ℕ):ℤ)/qInteger q ((d+1:ℕ):ℤ))*quantumHighestNorm q d c r := by
  have hrd:=channel_left_bound d c r
  have hrc:=channel_right_bound d c r
  have hLu:L-u.val=d-r.val:=by unfold coupledLabel at hL;omega
  have hcu:c-u.val=r.val:=by omega
  have hL':L=(d-r.val)+(c-r.val):=by unfold coupledLabel at hL;omega
  have hd:d=(d-r.val)+r.val:=by omega
  rw [quantumHighestNorm_closed q hq hq1,quantumHighestNorm_closed q hq hq1,
    hLu,hcu,hu,couplingNormClosed_bent q hq]
  rw [← hL',← hd,qnum_eq_qInteger q hq hq1,qnum_eq_qInteger q hq hq1]

end AMSPhysical
#print axioms AMSPhysical.quantumHighestNorm_bent
