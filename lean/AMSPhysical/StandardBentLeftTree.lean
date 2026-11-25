import StandardBentPairExpansion
import StandardLeftBoundaryExpansion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Whole-vector identification of the independent bent pair map with the
independent standard left coupling, including its exact scalar and phase. -/
theorem standardBentPairHighest_eq_leftTree (q:ℝ) (hq:0<q) (hq1:q≠1) (d c:ℕ)
    (r:Fin (min d c+1)) (a b:ℕ) (s:Fin (min a b+1))
    (hr:coupledLabel d c r=coupledLabel a b s)
    (u:Fin (min (coupledLabel a b s) c+1)) (hu:u.val=c-r.val):
    standardBentPairHighest q hq hq1 d c r a b s (coupledLabel a b s) hr rfl=
      (((-1:ℝ)^(r.val:ℤ))*Real.sqrt (quantumHighestNorm q (coupledLabel a b s) c u)/
        Real.sqrt (quantumHighestNorm q d c r)) •
      standardTypeIIBoundaryEquiv a b c (quantumLeftTreeHighest q hq hq1 a b c s u) := by
  have hrc:=channel_right_bound d c r
  rcases u with ⟨u,hub⟩
  simp only [Fin.val_mk] at hu
  subst u
  rw [standardBentPairHighest_expansion,standardLeftTreeHighest_boundary_expansion,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Fin.val_mk,Nat.sub_sub_self hrc,smul_smul]
  congr 1
  have hn:=ne_of_gt (Real.sqrt_pos.mpr
    (quantumHighestNorm_pos q hq (coupledLabel a b s) c ⟨c-r.val,hub⟩))
  field_simp [hn]

end AMSPhysical
#print axioms AMSPhysical.standardBentPairHighest_eq_leftTree
