import QuantumCupMonomial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupLeftRadial_factored (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n (quantumCupMonomial q n l h c (t+1) k))=
      quantumCupLeftDiagonal q n l h (t+1) k • quantumCupMonomial q n l h c (t+1) k+
        (q^(-2:ℤ))^(t+1) • ((tripleLeftCreation q n)^(t+2))
          (tripleLeftAnnihilation q n (((tripleRightCreation q n)^k)
            (tripleCupBase n (l-((t+1:ℕ):ℤ)) h (c-(k:ℤ))))) := by
  have h0:=tripleLeftAnnihilation_creation_power q hq hD n (l-((t+1:ℕ):ℤ)+h+(k:ℤ))
    _ (quantumCupRightPart_left_homogeneous q n l h c (t+1) k) t
  have h1:=congrArg (tripleLeftCreation q n) h0
  simp only [map_add,map_smul] at h1
  have hP (v : OccupationTripleLattice n →₀ ℝ) :
      tripleLeftCreation q n (((tripleLeftCreation q n)^(t+1)) v)=((tripleLeftCreation q n)^(t+2)) v :=
    (DFunLike.congr_fun (pow_succ' (tripleLeftCreation q n) (t+1)) v).symm
  have hP' (v : OccupationTripleLattice n →₀ ℝ) :
      tripleLeftCreation q n (((tripleLeftCreation q n)^t) v)=((tripleLeftCreation q n)^(t+1)) v :=
    (DFunLike.congr_fun (pow_succ' (tripleLeftCreation q n) t) v).symm
  rw [hP,hP',quantumCupLeftDiagonal_ladder] at h1
  exact h1.trans (add_comm _ _)

/-- The first physical radial operator has an explicitly derived bidiagonal
action on the cup monomials, before any Racah formula is introduced. -/
theorem quantumCupLeftRadial_positive (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t k : ℕ) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n (quantumCupMonomial q n l h c (t+1) (k+1)))=
      quantumCupLeftDiagonal q n l h (t+1) (k+1) • quantumCupMonomial q n l h c (t+1) (k+1)+
        quantumCupLeftOffDiagonal q n l h c (t+1) (k+1) • quantumCupMonomial q n l h c (t+2) k := by
  rw [quantumCupLeftRadial_factored q hq hD,tripleLeftAnnihilation_rightCup_power q hq hD n hn]
  simp only [map_smul,smul_smul]
  rw [quantumCupLeftOffDiagonal_cross q hq]
  have hl : l-((t+1:ℕ):ℤ)-1=l-((t+2:ℕ):ℤ) := by push_cast;ring
  have hc : c-((k+1:ℕ):ℤ)+1=c-(k:ℤ) := by push_cast;ring
  rw [hl,hc]
  rfl

theorem quantumCupLeftRadial_noRightCups (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (hn : 0<n) (l h c : ℤ) (t : ℕ) :
    tripleLeftCreation q n (tripleLeftAnnihilation q n (quantumCupMonomial q n l h c (t+1) 0))=
      quantumCupLeftDiagonal q n l h (t+1) 0 • quantumCupMonomial q n l h c (t+1) 0 := by
  rw [quantumCupLeftRadial_factored q hq hD]
  simp only [pow_zero,Module.End.one_apply,tripleLeftAnnihilation_cupBase_zero q n hn,map_zero,smul_zero,add_zero]

end AMSPhysical
#print axioms AMSPhysical.quantumCupLeftRadial_positive
