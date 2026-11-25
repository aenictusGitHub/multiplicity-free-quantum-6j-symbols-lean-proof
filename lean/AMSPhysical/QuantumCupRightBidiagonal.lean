import QuantumCupReverseMonomial
import QuantumTripleRightCrossPower

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupRightRadial_factored (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    tripleRightCreation q n (tripleRightAnnihilation q n (quantumCupMonomial q n l h c t (k+1)))=
      quantumCupLeftDiagonal q n c h (k+1) t • quantumCupMonomial q n l h c t (k+1)+
        (q^(-2:ℤ))^(k+1) • ((tripleRightCreation q n)^(k+2))
          (tripleRightAnnihilation q n (((tripleLeftCreation q n)^t)
            (tripleCupBase n (l-(t:ℤ)) h (c-((k+1:ℕ):ℤ))))) := by
  simp only [quantumCupMonomial_reverse q hq]
  have h0:=tripleRightAnnihilation_creation_power q hq hD n (c-((k+1:ℕ):ℤ)+h+(t:ℤ))
    _ (quantumCupLeftPart_right_homogeneous q n l h c t (k+1)) k
  have h1:=congrArg (tripleRightCreation q n) h0
  simp only [map_add,map_smul] at h1
  have hP (v : OccupationTripleLattice n →₀ ℝ) :
      tripleRightCreation q n (((tripleRightCreation q n)^(k+1)) v)=((tripleRightCreation q n)^(k+2)) v :=
    (DFunLike.congr_fun (pow_succ' (tripleRightCreation q n) (k+1)) v).symm
  have hP' (v : OccupationTripleLattice n →₀ ℝ) :
      tripleRightCreation q n (((tripleRightCreation q n)^k) v)=((tripleRightCreation q n)^(k+1)) v :=
    (DFunLike.congr_fun (pow_succ' (tripleRightCreation q n) k) v).symm
  rw [hP,hP',quantumCupLeftDiagonal_ladder] at h1
  exact h1.trans (add_comm _ _)

theorem quantumCupRightRadial_positive (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t k : ℕ) :
    tripleRightCreation q n (tripleRightAnnihilation q n (quantumCupMonomial q n l h c (t+1) (k+1)))=
      quantumCupLeftDiagonal q n c h (k+1) (t+1) • quantumCupMonomial q n l h c (t+1) (k+1)+
        quantumCupLeftOffDiagonal q n c h l (k+1) (t+1) • quantumCupMonomial q n l h c t (k+2) := by
  rw [quantumCupRightRadial_factored q hq hD,tripleRightAnnihilation_leftCup_power q hq hD n hn]
  simp only [map_smul,smul_smul]
  rw [quantumCupLeftOffDiagonal_cross q hq]
  have hl : l-((t+1:ℕ):ℤ)+1=l-(t:ℤ) := by push_cast;ring
  have hc : c-((k+1:ℕ):ℤ)-1=c-((k+2:ℕ):ℤ) := by push_cast;ring
  rw [hl,hc]
  simp only [quantumCupMonomial_reverse q hq]

theorem quantumCupRightRadial_noLeftCups (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (k : ℕ) :
    tripleRightCreation q n (tripleRightAnnihilation q n (quantumCupMonomial q n l h c 0 (k+1)))=
      quantumCupLeftDiagonal q n c h (k+1) 0 • quantumCupMonomial q n l h c 0 (k+1) := by
  rw [quantumCupRightRadial_factored q hq hD]
  simp only [pow_zero,Module.End.one_apply,tripleRightAnnihilation_cupBase_zero q n hn,map_zero,smul_zero,add_zero]

end AMSPhysical
#print axioms AMSPhysical.quantumCupRightRadial_positive
