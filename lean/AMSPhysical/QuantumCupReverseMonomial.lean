import QuantumCupMonomial
import QuantumTripleRightPowers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem quantumCupMonomial_reverse (q : ℝ) (hq : q≠0) (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    quantumCupMonomial q n l h c t k=
      ((tripleRightCreation q n)^k) (((tripleLeftCreation q n)^t) (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ)))) := by
  have hC : Commute (tripleLeftCreation q n) (tripleRightCreation q n) := tripleCreations_commute q hq n
  exact DFunLike.congr_fun (hC.pow_pow t k).eq (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ)))

theorem quantumCupLeftPart_right_homogeneous (q : ℝ) (n : ℕ) (l h c : ℤ) (t k : ℕ) :
    CoefficientHomogeneous (tripleRightDegree n) (c-(k:ℤ)+h+(t:ℤ))
      (((tripleLeftCreation q n)^t) (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ)))) := by
  have h0:=tripleLeftCreation_pow_right_homogeneous q n (h+(c-(k:ℤ))) _
    (tripleCupBase_right_homogeneous n (l-(t:ℤ)) h (c-(k:ℤ))) t
  have he : h+(c-(k:ℤ))+(t:ℤ)=c-(k:ℤ)+h+(t:ℤ) := by ring
  simpa only [he] using h0

end AMSPhysical
