import SearsFactorialTerm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem naturalSearsTerm_zero (q : ℝ) (hq : 0<q) (u r A B M S T k : ℕ)
    (hk : k≤u) (h : ¬RacahTermAdmissible u r A B M S k) :
    naturalSearsTerm q u r A B M S T k=0 := by
  by_cases hr : k≤r
  · by_cases hA : k≤A
    · by_cases hB : k≤B
      · by_cases hM : u-k≤M
        · by_cases hS : u-k≤S
          · exact False.elim (h ⟨hk,hr,hA,hB,hM,hS⟩)
          · simp only [naturalSearsTerm,qPochhammer_negative_phase_zero q hq S (u-k) (by omega),mul_zero]
        · simp only [naturalSearsTerm,qPochhammer_negative_phase_zero q hq M (u-k) (by omega),mul_zero,zero_mul]
      · simp only [naturalSearsTerm,qPochhammer_negative_phase_zero q hq B k (by omega),mul_zero,zero_mul,zero_div]
    · simp only [naturalSearsTerm,qPochhammer_negative_phase_zero q hq A k (by omega),mul_zero,zero_mul,zero_div]
  · simp only [naturalSearsTerm,qPochhammer_negative_phase_zero q hq r k (by omega),mul_zero,zero_mul,zero_div]

/-- All support restrictions are retained, so this identity includes physical
channels with a nonzero lower summation bound. -/
theorem naturalSearsTerm_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (u r A B M S T k : ℕ) (hk : k≤u) (hT : u≤T) (hrel : r+A+B+M+S+1=u+T) :
    naturalSearsTerm q u r A B M S T k=
      searsCommonPhase q u r M S*searsFactorialConstant q u r A B M S T*
        factorialRacahTerm q u r A B M S T k := by
  classical
  by_cases h : RacahTermAdmissible u r A B M S k
  · exact naturalSearsTerm_factorial_admissible q hq hq1 u r A B M S T k h hT hrel
  · rw [naturalSearsTerm_zero q hq u r A B M S T k hk h]
    unfold factorialRacahTerm
    rw [if_neg h,mul_zero]

theorem naturalSearsSum_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (u r A B M S T : ℕ) (hT : u≤T) (hrel : r+A+B+M+S+1=u+T) :
    (∑ k∈Finset.range (u+1),naturalSearsTerm q u r A B M S T k)=
      searsCommonPhase q u r M S*searsFactorialConstant q u r A B M S T*
        (∑ k∈Finset.range (u+1),factorialRacahTerm q u r A B M S T k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact naturalSearsTerm_factorial q hq hq1 u r A B M S T k
    (by have hh := Finset.mem_range.mp hk;omega) hT hrel

theorem searsCommonPhase_nonzero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (u r M S : ℕ) :
    searsCommonPhase q u r M S≠0 := by
  exact mul_ne_zero (pow_ne_zero _ (qInteger_denominator_ne_zero q hq hq1)) (zpow_ne_zero _ (ne_of_gt hq))

end AMSPhysical

#print axioms AMSPhysical.naturalSearsSum_factorial
