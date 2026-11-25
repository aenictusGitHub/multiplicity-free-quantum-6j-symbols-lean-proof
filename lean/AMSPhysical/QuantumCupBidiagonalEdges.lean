import QuantumCupLeftBidiagonal
import QuantumCupRightBidiagonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupLeftRadial_noLeftCups (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (k : ℕ) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n (quantumCupMonomial q n l h c 0 (k+1)))=
      quantumCupLeftOffDiagonal q n l h c 0 (k+1) • quantumCupMonomial q n l h c 1 k := by
  unfold quantumCupMonomial
  simp only [pow_zero,pow_one,Module.End.one_apply,Nat.cast_zero,sub_zero,Nat.cast_one]
  rw [tripleLeftAnnihilation_rightCup_power q hq hD n hn,map_smul]
  have hs:=quantumCupLeftOffDiagonal_cross q hq n l h c 0 (k+1)
  simp only [pow_zero,one_mul,Nat.cast_zero,sub_zero] at hs
  rw [hs]
  have hc : c-((k+1:ℕ):ℤ)+1=c-(k:ℤ) := by push_cast;ring
  rw [hc]

theorem quantumCupRightRadial_noRightCups (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t : ℕ) :
    tripleRightCreation q n (tripleRightAnnihilation q n (quantumCupMonomial q n l h c (t+1) 0))=
      quantumCupLeftOffDiagonal q n c h l 0 (t+1) • quantumCupMonomial q n l h c t 1 := by
  simp only [quantumCupMonomial_reverse q hq,pow_zero,pow_one,Module.End.one_apply,Nat.cast_zero,sub_zero,Nat.cast_one]
  rw [tripleRightAnnihilation_leftCup_power q hq hD n hn,map_smul]
  have hs:=quantumCupLeftOffDiagonal_cross q hq n c h l 0 (t+1)
  simp only [pow_zero,one_mul,Nat.cast_zero,sub_zero] at hs
  rw [hs]
  have hl : l-((t+1:ℕ):ℤ)+1=l-(t:ℤ) := by push_cast;ring
  rw [hl]

theorem quantumCupLeftRadial_all (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t k : ℕ) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n (quantumCupMonomial q n l h c t k))=
      quantumCupLeftDiagonal q n l h t k • quantumCupMonomial q n l h c t k+
        quantumCupLeftOffDiagonal q n l h c t k • quantumCupMonomial q n l h c (t+1) (k-1) := by
  cases t with
  | zero =>
    cases k with
    | zero =>
      simp only [quantumCupMonomial,pow_zero,Module.End.one_apply,Nat.cast_zero,sub_zero,
        tripleLeftAnnihilation_cupBase_zero q n hn,map_zero,quantumCupLeftDiagonal,
        quantumCupLeftOffDiagonal,Nat.cast_zero,qInteger_zero,mul_zero,zero_mul,zero_smul,add_zero]
    | succ k =>
      rw [quantumCupLeftRadial_noLeftCups q hq hD n hn]
      simp only [quantumCupLeftDiagonal,Nat.cast_zero,qInteger_zero,mul_zero,zero_mul,zero_smul,zero_add,Nat.add_sub_cancel]
  | succ t =>
    cases k with
    | zero =>
      rw [quantumCupLeftRadial_noRightCups q hq hD n hn]
      simp only [quantumCupLeftOffDiagonal,Nat.cast_zero,qInteger_zero,mul_zero,zero_smul,add_zero]
    | succ k =>
      simpa only [Nat.add_sub_cancel] using quantumCupLeftRadial_positive q hq hD n hn l h c t k

theorem quantumCupRightRadial_all (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t k : ℕ) :
    tripleRightCreation q n (tripleRightAnnihilation q n (quantumCupMonomial q n l h c t k))=
      quantumCupLeftDiagonal q n c h k t • quantumCupMonomial q n l h c t k+
        quantumCupLeftOffDiagonal q n c h l k t • quantumCupMonomial q n l h c (t-1) (k+1) := by
  cases k with
  | zero =>
    cases t with
    | zero =>
      simp only [quantumCupMonomial,pow_zero,Module.End.one_apply,Nat.cast_zero,sub_zero,
        tripleRightAnnihilation_cupBase_zero q n hn,map_zero,quantumCupLeftDiagonal,
        quantumCupLeftOffDiagonal,Nat.cast_zero,qInteger_zero,mul_zero,zero_mul,zero_smul,add_zero]
    | succ t =>
      rw [quantumCupRightRadial_noRightCups q hq hD n hn]
      simp only [quantumCupLeftDiagonal,Nat.cast_zero,qInteger_zero,mul_zero,zero_mul,zero_smul,zero_add,Nat.add_sub_cancel]
  | succ k =>
    cases t with
    | zero =>
      rw [quantumCupRightRadial_noLeftCups q hq hD n hn]
      simp only [quantumCupLeftOffDiagonal,Nat.cast_zero,qInteger_zero,mul_zero,zero_smul,add_zero]
    | succ t =>
      simpa only [Nat.add_sub_cancel] using quantumCupRightRadial_positive q hq hD n hn l h c t k

end AMSPhysical
#print axioms AMSPhysical.quantumCupLeftRadial_all
#print axioms AMSPhysical.quantumCupRightRadial_all
