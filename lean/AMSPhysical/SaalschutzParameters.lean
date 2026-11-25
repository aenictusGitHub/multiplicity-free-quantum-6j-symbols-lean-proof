import QShiftedFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

structure SaalschutzGeneric (Q A B C : ℝ) : Prop where
  ne_zero : C≠0
  notPower : ∀ z : ℤ,C≠Q^z
  notScaledPower : ∀ z : ℤ,C≠A*B*Q^z

theorem power_ratio_unique (Q : ℝ) (hQ : Q≠0) (C D : ℝ) (a b : ℤ)
    (h : C*Q^a=D*Q^b) : C=D*Q^(b-a) := by
  have he := congrArg (fun x : ℝ => x*Q^(-a)) h
  dsimp only at he
  rw [mul_assoc,mul_assoc,← zpow_add₀ hQ,← zpow_add₀ hQ,add_neg_cancel,zpow_zero,mul_one] at he
  simpa only [sub_eq_add_neg] using he

theorem SaalschutzGeneric.C_power_ne_one {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (k : ℤ) : C*Q^k≠1 := by
  intro he
  have hh : C*Q^k=1*Q^(0:ℤ) := by simpa only [zpow_zero,mul_one,one_mul] using he
  have hz := power_ratio_unique Q hQ C 1 k 0 hh
  exact h.notPower (-k) (by simpa only [zero_sub,one_mul] using hz)

theorem SaalschutzGeneric.C_factor {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (k : ℕ) : 1-C*Q^k≠0 := by
  intro he
  exact h.C_power_ne_one hQ k (by rw [zpow_natCast];linarith)

theorem SaalschutzGeneric.scaled_factor {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (z : ℤ) (k : ℕ) : 1-(A*B*Q^z/C)*Q^k≠0 := by
  intro he
  apply h.notScaledPower (z+(k:ℤ))
  rw [zpow_add₀ hQ,zpow_natCast]
  field_simp [h.ne_zero] at he
  linear_combination he

theorem SaalschutzGeneric.C_over_AB_factor {Q A B C : ℝ} (h : SaalschutzGeneric Q A B C)
    (hQ : Q≠0) (hA : A≠0) (hB : B≠0) (k : ℕ) : 1-(C/(A*B))*Q^k≠0 := by
  intro he
  have he' : C*Q^(k:ℤ)=(A*B)*Q^(0:ℤ) := by
    field_simp [hA,hB] at he
    rw [zpow_natCast,zpow_zero,mul_one]
    linear_combination -he
  have hz := power_ratio_unique Q hQ C (A*B) k 0 he'
  exact h.notScaledPower (-(k:ℤ)) (by simpa only [zero_sub] using hz)

theorem baseQ_factor_nonzero (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≠1) (k : ℕ) : 1-Q*Q^k≠0 := by
  intro he
  have hp : Q^((k+1:ℕ):ℤ)=1 := by rw [zpow_natCast,pow_succ'];linarith
  have hz := (zpow_eq_one_iff_right₀ hQ.le hQ1).mp hp
  omega

theorem saalschutz_Poch_den_nonzero (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (h : SaalschutzGeneric Q A B C) (n k : ℕ) :
    qPochhammer Q Q k*qPochhammer Q C k*qPochhammer Q (A*B*Q^(1-(n:ℤ))/C) k≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (qPochhammer_ne_zero Q Q k (fun i _ => baseQ_factor_nonzero Q hQ hQ1 i))
      (qPochhammer_ne_zero Q C k (fun i _ => h.C_factor (ne_of_gt hQ) i))
  · exact qPochhammer_ne_zero _ _ k (fun i _ => h.scaled_factor (ne_of_gt hQ) _ i)

def saalschutzTerm (Q A B C : ℝ) (n k : ℕ) : ℝ :=
  qPochhammer Q A k*qPochhammer Q B k*qPochhammer Q (Q^(-(n:ℤ))) k*Q^k/
    (qPochhammer Q Q k*qPochhammer Q C k*qPochhammer Q (A*B*Q^(1-(n:ℤ))/C) k)

def saalschutzSum (Q A B C : ℝ) (n : ℕ) : ℝ := ∑ k∈Finset.range (n+1),saalschutzTerm Q A B C n k

def saalschutzProduct (Q A B C : ℝ) (n : ℕ) : ℝ :=
  qPochhammer Q (C/A) n*qPochhammer Q (C/B) n/
    (qPochhammer Q C n*qPochhammer Q (C/(A*B)) n)

theorem saalschutzTerm_zero (Q A B C : ℝ) (n : ℕ) : saalschutzTerm Q A B C n 0=1 := by
  simp only [saalschutzTerm,qPochhammer_zero,pow_zero,one_mul,div_one]

theorem saalschutzTerm_terminates (Q A B C : ℝ) (hQ : Q≠0) (n k : ℕ) (hk : n<k) :
    saalschutzTerm Q A B C n k=0 := by
  rw [saalschutzTerm,qPochhammer_terminates Q hQ n k hk,mul_zero,zero_mul,zero_div]

end AMSPhysical

#print axioms AMSPhysical.saalschutz_Poch_den_nonzero
