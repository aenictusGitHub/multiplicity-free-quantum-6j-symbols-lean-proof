import SpinRacahFactorialSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def zeroRacahTerm (q : ℝ) (u r A B M S T : ℕ) : ℝ :=
  qfactorial q T/(qfactorial q u*qfactorial q r*qfactorial q A*qfactorial q B*
    qfactorial q (M-u)*qfactorial q (S-u))

theorem zeroRacahTerm_pos (q : ℝ) (hq : 0<q) (u r A B M S T : ℕ) :
    0<zeroRacahTerm q u r A B M S T := by
  exact div_pos (qfactorial_pos q hq _)
    (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))
      (qfactorial_pos q hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))

theorem factorialRacahSum_single (q : ℝ) (u r A B M S T : ℕ)
    (hM : u≤M) (hS : u≤S) (hb : r=0 ∨ B=0) :
    (∑ k∈Finset.range (u+1),factorialRacahTerm q u r A B M S T k)=zeroRacahTerm q u r A B M S T := by
  classical
  rw [Finset.sum_eq_single 0]
  · unfold factorialRacahTerm zeroRacahTerm
    rw [if_pos (show RacahTermAdmissible u r A B M S 0 from ⟨by omega,by omega,by omega,by omega,by simpa using hM,by simpa using hS⟩)]
    simp only [Nat.sub_zero,pow_zero,one_mul,qfactorial_zero,mul_one]
  · intro k hk hk0
    have hbad : ¬RacahTermAdmissible u r A B M S k := by
      intro h
      rcases hb with hr | hB
      · have hh := h.2.1
        omega
      · have hh := h.2.2.2.1
        omega
    simp only [factorialRacahTerm,if_neg hbad]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

end AMSPhysical

#print axioms AMSPhysical.factorialRacahSum_single
