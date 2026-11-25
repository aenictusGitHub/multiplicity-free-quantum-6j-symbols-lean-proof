import SearsQuantumPhase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def naturalSearsTerm (q : ℝ) (u r A B M S T k : ℕ) : ℝ :=
  (qPochhammer (q^2) (q^(-2*(u:ℤ))) k*qPochhammer (q^2) (q^(-2*(r:ℤ))) k*
    qPochhammer (q^2) (q^(-2*(A:ℤ))) k*qPochhammer (q^2) (q^(-2*(B:ℤ))) k)/
      (qPochhammer (q^2) (q^2) k*qPochhammer (q^2) (q^(-2*(T:ℤ))) k)*
      q^(2*(-(r:ℤ))*((u-k:ℕ):ℤ))*q^(2*((u:ℤ)-(r:ℤ)-(M:ℤ)-(S:ℤ)-1)*(k:ℤ))*
      q^(2*(k:ℤ)*((u-k+1:ℕ):ℤ))*qPochhammer (q^2) (q^(-2*(M:ℤ))) (u-k)*
      qPochhammer (q^2) (q^(-2*(S:ℤ))) (u-k)

def RacahTermAdmissible (u r A B M S k : ℕ) : Prop :=
  k≤u ∧ k≤r ∧ k≤A ∧ k≤B ∧ u-k≤M ∧ u-k≤S

def factorialRacahTerm (q : ℝ) (u r A B M S T k : ℕ) : ℝ := by
  classical
  exact if RacahTermAdmissible u r A B M S k then
    (-1:ℝ)^k*qfactorial q (T-k)/
      (qfactorial q k*qfactorial q (u-k)*qfactorial q (r-k)*qfactorial q (A-k)*
        qfactorial q (B-k)*qfactorial q (M-(u-k))*qfactorial q (S-(u-k))) else 0

def searsFactorialConstant (q : ℝ) (u r A B M S T : ℕ) : ℝ :=
  qfactorial q u*qfactorial q r*qfactorial q A*qfactorial q B*qfactorial q M*qfactorial q S/qfactorial q T

def searsCommonPhase (q : ℝ) (u r M S : ℕ) : ℝ :=
  (q-q⁻¹)^(2*u)*q^(-((M:ℤ)+2*(r:ℤ)+(S:ℤ))*(u:ℤ)+2*(u.choose 2:ℤ))

theorem qPochhammer_negative_phase_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a k : ℕ) (hk : k≤a) : qPochhammer (q^2) (q^(-2*(a:ℤ))) k=
      negativePochPhase q a k*(qfactorial q a/qfactorial q (a-k)) := by
  rw [qPochhammer_negative_factorial q hq hq1 a k hk]
  unfold negativePochPhase
  ring

theorem qPochhammer_negative_phase_zero (q : ℝ) (hq : 0<q) (a k : ℕ) (hk : a<k) :
    qPochhammer (q^2) (q^(-2*(a:ℤ))) k=0 := by
  have he : q^(-2*(a:ℤ))=(q^2)^(-(a:ℤ)) := by rw [square_zpow_even];congr 1;ring
  rw [he]
  exact qPochhammer_terminates (q^2) (pow_ne_zero 2 (ne_of_gt hq)) a k hk

/-- Each admissible cleared Sears summand is exactly the seven-denominator
quantum-factorial Racah summand, with a common, explicitly checked phase. -/
theorem naturalSearsTerm_factorial_admissible (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (u r A B M S T k : ℕ) (h : RacahTermAdmissible u r A B M S k)
    (hT : u≤T) (hrel : r+A+B+M+S+1=u+T) :
    naturalSearsTerm q u r A B M S T k=
      searsCommonPhase q u r M S*searsFactorialConstant q u r A B M S T*
        factorialRacahTerm q u r A B M S T k := by
  rcases h with ⟨hku,hkr,hkA,hkB,hM,hS⟩
  have hfull : RacahTermAdmissible u r A B M S k := ⟨hku,hkr,hkA,hkB,hM,hS⟩
  have hphase := sears_quantum_phase q hq hq1 u r A B M S T k hku hrel
  unfold naturalSearsTerm
  rw [qPochhammer_negative_phase_factorial q hq hq1 u k hku,
    qPochhammer_negative_phase_factorial q hq hq1 r k hkr,
    qPochhammer_negative_phase_factorial q hq hq1 A k hkA,
    qPochhammer_negative_phase_factorial q hq hq1 B k hkB,
    qPochhammer_negative_phase_factorial q hq hq1 T k (by omega),
    qPochhammer_negative_phase_factorial q hq hq1 M (u-k) hM,
    qPochhammer_negative_phase_factorial q hq hq1 S (u-k) hS,
    qPochhammer_base_factorial q hq hq1 k]
  change _ = _
  have hbase : (-(q-q⁻¹))^k*q^((k:ℤ)+(k.choose 2:ℤ))=basePochPhase q k := rfl
  rw [hbase]
  calc
    _ = ((negativePochPhase q u k*negativePochPhase q r k*negativePochPhase q A k*negativePochPhase q B k)/
        (basePochPhase q k*negativePochPhase q T k)*
        q^(2*(-(r:ℤ))*((u-k:ℕ):ℤ))*q^(2*((u:ℤ)-(r:ℤ)-(M:ℤ)-(S:ℤ)-1)*(k:ℤ))*
        q^(2*(k:ℤ)*((u-k+1:ℕ):ℤ))*negativePochPhase q M (u-k)*negativePochPhase q S (u-k))*
      (searsFactorialConstant q u r A B M S T*qfactorial q (T-k)/
        (qfactorial q k*qfactorial q (u-k)*qfactorial q (r-k)*qfactorial q (A-k)*
          qfactorial q (B-k)*qfactorial q (M-(u-k))*qfactorial q (S-(u-k)))) := by
      unfold searsFactorialConstant
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    _ = _ := by
      rw [hphase]
      unfold factorialRacahTerm searsCommonPhase
      rw [if_pos hfull]
      ring

end AMSPhysical

#print axioms AMSPhysical.naturalSearsTerm_factorial_admissible
