import RacahTriangleWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
noncomputable section
namespace AMSPhysical

def boundaryFirstLeftWeight (q : ℝ) (a b c u v : ℕ) : ℝ :=
  qnum q (a+c+u+v+1)*
    (qfactorial q (a+v)*qfactorial q (c+u)/qfactorial q (a+c+u+v+1))*
    (qfactorial q (u+v)*qfactorial q (a+c)*qfactorial q b/qfactorial q (a+b+c+u+v+1))
def boundaryFirstRightWeight (q : ℝ) (a b c u v : ℕ) : ℝ :=
  qnum q (b+c+v+1)*
    (qfactorial q u*qfactorial q c*qfactorial q (b+v)/qfactorial q (b+c+u+v+1))*
    (qfactorial q v*qfactorial q a*qfactorial q (b+c)/qfactorial q (a+b+c+v+1))
def boundaryFirstKernel (q : ℝ) (a b c u v : ℕ) : ℝ :=
  qfactorial q (a+b+c+u+v+1)/
    (qfactorial q u*qfactorial q a*qfactorial q b*qfactorial q c*qfactorial q v)

theorem racah_first_boundary_square (q : ℝ) (hq : 0<q) (a b c u v : ℕ) :
    couplingNormClosed q (a+c) b (u+v)/
      (couplingNormClosed q c (b+v) u*couplingNormClosed q a (b+c) v)*
      (q^(-(v:ℤ)*((c+u:ℕ):ℤ))*qfactorial q (b+v)*qfactorial q (b+c)/
        (qfactorial q (b+c+v)*qfactorial q b))^2=
      boundaryFirstLeftWeight q a b c u v*boundaryFirstRightWeight q a b c u v*
        (boundaryFirstKernel q a b c u v)^2 := by
  have hq0 := ne_of_gt hq
  have hphase : q^(-2*((u+v:ℕ):ℤ)*(b:ℤ))*(q^(-(v:ℤ)*((c+u:ℕ):ℤ)))^2=
      q^(-2*(u:ℤ)*((b+v:ℕ):ℤ))*q^(-2*(v:ℤ)*((b+c:ℕ):ℤ)) := by
    rw [sq,← zpow_add₀ hq0,← zpow_add₀ hq0,← zpow_add₀ hq0]
    congr 1
    push_cast
    ring
  unfold couplingNormClosed boundaryFirstLeftWeight boundaryFirstRightWeight boundaryFirstKernel
  have hFi := qfactorial_succ q (a+c+u+v)
  have hFj := qfactorial_succ q (b+c+v)
  simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hFi hFj hphase ⊢
  rw [hFi,hFj]
  have hqi : qnum q (a+(c+(u+(v+1))))≠0 := ne_of_gt (qnum_pos q hq _ (by omega))
  have hqj : qnum q (b+(c+(v+1)))≠0 := ne_of_gt (qnum_pos q hq _ (by omega))
  field_simp [hqi,hqj,qfactorial_ne_zero q hq,
    ne_of_gt (qnum_pos q hq (a+c+u+v+1) (by omega)),
    ne_of_gt (qnum_pos q hq (b+c+v+1) (by omega)),
    zpow_ne_zero (-2*(u:ℤ)*((b+v:ℕ):ℤ)) hq0,
    zpow_ne_zero (-2*(v:ℤ)*((b+c:ℕ):ℤ)) hq0]
  linear_combination hphase

def boundaryLastLeftWeight (q : ℝ) (a b c u r : ℕ) : ℝ :=
  qnum q (a+b+c+u+1)*
    (qfactorial q r*qfactorial q (a+c)*qfactorial q (b+u)/qfactorial q (a+b+c+u+r+1))*
    (qfactorial q (c+u)*qfactorial q (a+b)/qfactorial q (a+b+c+u+1))
def boundaryLastRightWeight (q : ℝ) (a b c u r : ℕ) : ℝ :=
  qnum q (b+c+r+1)*
    (qfactorial q u*qfactorial q (b+r)*qfactorial q c/qfactorial q (b+c+r+u+1))*
    (qfactorial q (c+r)*qfactorial q a*qfactorial q b/qfactorial q (a+b+c+r+1))
def boundaryLastKernel (q : ℝ) (a b c u r : ℕ) : ℝ :=
  qfactorial q (a+b+c+u+r+1)/
    (qfactorial q u*qfactorial q r*qfactorial q a*qfactorial q b*qfactorial q c)

theorem racah_last_boundary_square (q : ℝ) (hq : 0<q) (a b c u r : ℕ) :
    (couplingNormClosed q (a+c) (b+u) r*couplingNormClosed q (a+b) 0 (c+u))/
      (couplingNormClosed q (b+r) c u*couplingNormClosed q a b (c+r))*
      (q^(((c+u:ℕ):ℤ)*(r:ℤ)-((b+r+u:ℕ):ℤ)*(c:ℤ))*qfactorial q (c+r)*qfactorial q (b+r)/
        (qfactorial q (b+c+r)*qfactorial q r))^2=
      boundaryLastLeftWeight q a b c u r*boundaryLastRightWeight q a b c u r*
        (boundaryLastKernel q a b c u r)^2 := by
  have hq0 := ne_of_gt hq
  have hphase : q^(-2*(r:ℤ)*((b+u:ℕ):ℤ))*
      (q^(((c+u:ℕ):ℤ)*(r:ℤ)-((b+r+u:ℕ):ℤ)*(c:ℤ)))^2=
      q^(-2*(u:ℤ)*(c:ℤ))*q^(-2*((c+r:ℕ):ℤ)*(b:ℤ)) := by
    rw [sq,← zpow_add₀ hq0,← zpow_add₀ hq0,← zpow_add₀ hq0]
    congr 1
    push_cast
    ring
  unfold couplingNormClosed boundaryLastLeftWeight boundaryLastRightWeight boundaryLastKernel
  simp only [Nat.cast_zero,mul_zero,zpow_zero,one_mul,qfactorial_zero,mul_one]
  have hFi := qfactorial_succ q (a+b+c+u)
  have hFj := qfactorial_succ q (b+c+r)
  simp only [Nat.add_zero,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] at hFi hFj hphase ⊢
  rw [hFi,hFj]
  have hqi : qnum q (a+(b+(c+(u+1))))≠0 := ne_of_gt (qnum_pos q hq _ (by omega))
  have hqj : qnum q (b+(c+(r+1)))≠0 := ne_of_gt (qnum_pos q hq _ (by omega))
  field_simp [hqi,hqj,qfactorial_ne_zero q hq,
    ne_of_gt (qnum_pos q hq (a+b+c+u+1) (by omega)),
    ne_of_gt (qnum_pos q hq (b+c+r+1) (by omega)),
    zpow_ne_zero (-2*(u:ℤ)*(c:ℤ)) hq0,
    zpow_ne_zero (-2*((c+r:ℕ):ℤ)*(b:ℤ)) hq0]
  linear_combination hphase

end AMSPhysical

#print axioms AMSPhysical.racah_first_boundary_square
#print axioms AMSPhysical.racah_last_boundary_square
