import AMSDynkinVertexPhase

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem amsDynkinVertexPhase_mixed_defect (n : ℕ) (hn : 2≤n) (p s k : ℕ)
    (hs : 0<s) (a c : Fin n → ℤ)
    (hdef : dynkinBox n a+dynkinBox n (mixedHighestDynkin n p s)-dynkinBox n c =
      ((n+1:ℕ):ℤ)*(k:ℤ)) :
    amsDynkinVertexPhase n a (mixedHighestDynkin n p s) c=(-1:ℝ)^((n-1)*k) := by
  unfold amsDynkinVertexPhase
  rw [if_neg (by rw [mixedHighestDynkin_pure_symmetric_iff n hn];omega),hdef]
  have hN : ((n+1:ℕ):ℤ)≠0 := by omega
  rw [Int.mul_ediv_cancel_left _ hN,Int.toNat_natCast]

theorem amsDynkinVertexPhase_forward (n : ℕ) (hn : 2≤n) (p s r : ℕ) :
    amsDynkinVertexPhase n (mixedHighestDynkin n (p+r) 0)
      (mixedHighestDynkin n 0 (s+r)) (mixedHighestDynkin n p s) =
        (-1:ℝ)^((n-1)*r) := by
  by_cases hb : s+r=0
  · have hs : s=0 := by omega
    have hr : r=0 := by omega
    simp only [hs,hr,Nat.add_zero,Nat.mul_zero,pow_zero]
    exact amsDynkinVertexPhase_symmetric_second n 0 _ _
  · apply amsDynkinVertexPhase_mixed_defect n hn 0 (s+r) r (by omega)
    rw [dynkinBox_mixed n (by omega),dynkinBox_mixed n (by omega),dynkinBox_mixed n (by omega)]
    push_cast
    ring

theorem amsDynkinVertexPhase_reverse (n p s r : ℕ) :
    amsDynkinVertexPhase n (mixedHighestDynkin n 0 (s+r))
      (mixedHighestDynkin n (p+r) 0) (mixedHighestDynkin n p s)=1 :=
  amsDynkinVertexPhase_symmetric_second n (p+r) _ _

theorem amsDynkinVertexPhase_mixed_sym (n p s c d : ℕ) :
    amsDynkinVertexPhase n (mixedHighestDynkin n p s)
      (mixedHighestDynkin n c 0) (mixedHighestDynkin n d 0)=1 :=
  amsDynkinVertexPhase_symmetric_second n c _ _

theorem amsDynkinVertexPhase_sym_mixed (n : ℕ) (hn : 2≤n) (a p s d : ℕ)
    (hbal : a+p=s+d) :
    amsDynkinVertexPhase n (mixedHighestDynkin n a 0)
      (mixedHighestDynkin n p s) (mixedHighestDynkin n d 0)=(-1:ℝ)^((n-1)*s) := by
  by_cases hs : s=0
  · subst s
    simp only [Nat.mul_zero,pow_zero]
    exact amsDynkinVertexPhase_symmetric_second n p _ _
  · apply amsDynkinVertexPhase_mixed_defect n hn p s s (by omega)
    rw [dynkinBox_mixed n (by omega),dynkinBox_mixed n (by omega),dynkinBox_mixed n (by omega)]
    have hb : (a:ℤ)+(p:ℤ)=(s:ℤ)+(d:ℤ) := by exact_mod_cast hbal
    push_cast
    nlinarith

theorem amsDynkinVertexPhase_twoRow_sym_opp (n : ℕ) (hn : 2≤n)
    (a : Fin n → ℤ) (c d : ℕ) (ha : dynkinBox n a=(c:ℤ)+(d:ℤ)) :
    amsDynkinVertexPhase n a (mixedHighestDynkin n 0 c) (mixedHighestDynkin n d 0)=
      (-1:ℝ)^((n-1)*c) := by
  by_cases hc : c=0
  · subst c
    simp only [Nat.mul_zero,pow_zero]
    exact amsDynkinVertexPhase_symmetric_second n 0 _ _
  · apply amsDynkinVertexPhase_mixed_defect n hn 0 c c (by omega)
    rw [ha,dynkinBox_mixed n (by omega),dynkinBox_mixed n (by omega)]
    push_cast
    ring

end AMSPhysical
#print axioms AMSPhysical.amsDynkinVertexPhase_forward
#print axioms AMSPhysical.amsDynkinVertexPhase_sym_mixed
