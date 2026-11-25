import QuantumCupBidiagonalEdges

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def quantumCupRankGauge (n t : ℕ) : ℝ := (-1:ℝ)^((n-1)*t)

theorem quantumCupRankGauge_ne_zero (n t : ℕ) : quantumCupRankGauge n t≠0 := by
  unfold quantumCupRankGauge
  exact pow_ne_zero _ (by norm_num)

theorem quantumCupRankGauge_succ (n t : ℕ) :
    quantumCupRankGauge n (t+1)=quantumCupRankGauge n t*(-1:ℝ)^(n-1) := by
  simp only [quantumCupRankGauge,Nat.mul_add,Nat.mul_one,pow_add]

theorem quantumCupLeftDiagonal_rank_shift (q : ℝ) (n : ℕ) (l h : ℤ) (t k : ℕ) :
    quantumCupLeftDiagonal q n l h t k=quantumCupLeftDiagonal q 1 l (h+(n:ℤ)-1) t k := by
  unfold quantumCupLeftDiagonal
  simp only [Nat.cast_one]
  have he : -l-(h+(n:ℤ)-1)-(t:ℤ)-(k:ℤ)-1+2= -l-h-(t:ℤ)-(k:ℤ)-(n:ℤ)+2 := by ring
  have he' : l+(h+(n:ℤ)-1)+(k:ℤ)+1=l+h+(k:ℤ)+(n:ℤ) := by ring
  rw [he,he']

theorem quantumCupLeftOffDiagonal_rank_shift (q : ℝ) (n : ℕ) (hn : 0<n)
    (l h c : ℤ) (t k : ℕ) :
    quantumCupLeftOffDiagonal q n l h c t k=
      (-1:ℝ)^(n-1)*quantumCupLeftOffDiagonal q 1 l (h+(n:ℤ)-1) c t k := by
  have hpow : (-1:ℝ)^n=(-1:ℝ)^(n-1)*(-1) := by
    calc
      _ = (-1:ℝ)^((n-1)+1) := by congr 1;omega
      _ = _ := by rw [pow_succ]
  unfold quantumCupLeftOffDiagonal
  simp only [pow_one,Nat.cast_one]
  have he : 1-1-(h+(n:ℤ)-1)-c-2*(t:ℤ)=1-(n:ℤ)-h-c-2*(t:ℤ) := by ring
  rw [he,hpow]
  ring

/-- The literal cup-basis sign intertwines the first rank-shifted coefficient
system; it is derived from occupation operators rather than fitted overlaps. -/
theorem quantumCupRankGauge_left_off (q : ℝ) (n : ℕ) (hn : 0<n)
    (l h c : ℤ) (t k : ℕ) :
    quantumCupLeftOffDiagonal q n l h c t k*quantumCupRankGauge n (t+1)=
      quantumCupRankGauge n t*quantumCupLeftOffDiagonal q 1 l (h+(n:ℤ)-1) c t k := by
  rw [quantumCupLeftOffDiagonal_rank_shift q n hn,quantumCupRankGauge_succ]
  have hs : (-1:ℝ)^(n-1)*(-1:ℝ)^(n-1)=1 := by rw [← mul_pow];norm_num
  calc
    _ = quantumCupRankGauge n t*quantumCupLeftOffDiagonal q 1 l (h+(n:ℤ)-1) c t k*
      ((-1:ℝ)^(n-1)*(-1:ℝ)^(n-1)) := by ring
    _ = _ := by rw [hs,mul_one]

theorem quantumCupRankGauge_right_off (q : ℝ) (n : ℕ) (hn : 0<n)
    (l h c : ℤ) (t k : ℕ) :
    quantumCupLeftOffDiagonal q n c h l k (t+1)*quantumCupRankGauge n t=
      quantumCupRankGauge n (t+1)*quantumCupLeftOffDiagonal q 1 c (h+(n:ℤ)-1) l k (t+1) := by
  rw [quantumCupLeftOffDiagonal_rank_shift q n hn,quantumCupRankGauge_succ]
  ring

end AMSPhysical
