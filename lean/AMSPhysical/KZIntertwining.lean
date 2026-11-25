import HilbertMatrixReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped ComplexOrder

theorem unitaryConj_of_intertwining (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (S : unitary (CStarMatrix (Fin n) (Fin n) ℂ))
    (h : b*(S:CStarMatrix (Fin n) (Fin n) ℂ)=(S:CStarMatrix (Fin n) (Fin n) ℂ)*a) :
    b=unitaryConj S a := by
  have he := congrArg (fun x : CStarMatrix (Fin n) (Fin n) ℂ =>
    x*star (S:CStarMatrix (Fin n) (Fin n) ℂ)) h
  have hs : (S:CStarMatrix (Fin n) (Fin n) ℂ)*star (S:CStarMatrix (Fin n) (Fin n) ℂ)=1 :=
    (unitary.mem_iff.mp S.property).2
  simpa only [unitaryConj,mul_assoc,hs,mul_one] using he

theorem kzConnection_intertwining (n : ℕ) (a b a' b' : CStarMatrix (Fin n) (Fin n) ℂ)
    (ha : star a= -a) (hb : star b= -b) (ha' : star a'= -a') (hb' : star b'= -b')
    (S : unitary (CStarMatrix (Fin n) (Fin n) ℂ))
    (h₁ : a'*(S:CStarMatrix (Fin n) (Fin n) ℂ)=(S:CStarMatrix (Fin n) (Fin n) ℂ)*a)
    (h₂ : b'*(S:CStarMatrix (Fin n) (Fin n) ℂ)=(S:CStarMatrix (Fin n) (Fin n) ℂ)*b) :
    (kzConnection n a' b' ha' hb' : CStarMatrix (Fin n) (Fin n) ℂ)=
      unitaryConj S (kzConnection n a b ha hb : CStarMatrix (Fin n) (Fin n) ℂ) := by
  have h₁e := unitaryConj_of_intertwining n a a' S h₁
  have h₂e := unitaryConj_of_intertwining n b b' S h₂
  subst a'
  subst b'
  exact kzConnection_conj n a b ha hb S

def imaginaryResidue (n : ℕ) (t : ℝ) (A : CStarMatrix (Fin n) (Fin n) ℂ) :
    CStarMatrix (Fin n) (Fin n) ℂ := ((t:ℂ)*Complex.I) • A

theorem imaginaryResidue_skew (n : ℕ) (t : ℝ) (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hA : IsSelfAdjoint A) : star (imaginaryResidue n t A)= -imaginaryResidue n t A := by
  simp [imaginaryResidue,star_smul,hA.star_eq]

theorem imaginaryResidue_intertwining (n : ℕ) (t : ℝ) (A B S : CStarMatrix (Fin n) (Fin n) ℂ)
    (h : B*S=S*A) : imaginaryResidue n t B*S=S*imaginaryResidue n t A := by
  simp only [imaginaryResidue,smul_mul_assoc,mul_smul_comm,h]

/-- Naturality of the constructed KZ connection for every imaginary deformation parameter,
derived from a simultaneous unitary intertwiner of the Hermitian residues. -/
theorem hermitianPair_KZ_intertwining (n : ℕ) (A B A' B' : CStarMatrix (Fin n) (Fin n) ℂ)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hA' : IsSelfAdjoint A') (hB' : IsSelfAdjoint B')
    (S : unitary (CStarMatrix (Fin n) (Fin n) ℂ))
    (h₁ : A'*(S:CStarMatrix (Fin n) (Fin n) ℂ)=(S:CStarMatrix (Fin n) (Fin n) ℂ)*A)
    (h₂ : B'*(S:CStarMatrix (Fin n) (Fin n) ℂ)=(S:CStarMatrix (Fin n) (Fin n) ℂ)*B) (t : ℝ) :
    (kzConnection n (imaginaryResidue n t A') (imaginaryResidue n t B')
      (imaginaryResidue_skew n t A' hA') (imaginaryResidue_skew n t B' hB') :
        CStarMatrix (Fin n) (Fin n) ℂ)=
      unitaryConj S (kzConnection n (imaginaryResidue n t A) (imaginaryResidue n t B)
        (imaginaryResidue_skew n t A hA) (imaginaryResidue_skew n t B hB) :
          CStarMatrix (Fin n) (Fin n) ℂ) :=
  kzConnection_intertwining n _ _ _ _ _ _ _ _ S
    (imaginaryResidue_intertwining n t A A' _ h₁) (imaginaryResidue_intertwining n t B B' _ h₂)

end AMSPhysical

#print axioms AMSPhysical.hermitianPair_KZ_intertwining
