import QuantumOccupationLowering
import FiniteWeightedHilbert
import BilinearAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

/-- A weighted occupation-graph adjoint criterion, with all zero-source
boundaries included. Both maps are actual endomorphisms of the finite module. -/
theorem occupation_E_adjoint_of_edges (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (i : Fin n) (w : occupationWeights (Fin (n+1)) L → ℝ)
    (T : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L))
    (c : occupationWeights (Fin (n+1)) L → ℝ)
    (hT : ∀ x (hi : 0<x.val i.succ),T (quantumOccupationBasis (K:=ℝ) L (raisedOccupation n L x i hi))=
      c x • quantumOccupationBasis (K:=ℝ) L x)
    (hT0 : ∀ y,y.val i.castSucc=0 → T (quantumOccupationBasis (K:=ℝ) L y)=0)
    (hstep : ∀ x (hi : 0<x.val i.succ),qInteger q (x.val i.succ)*w (raisedOccupation n L x i hi)=c x*w x) :
    PairAdjoint (finiteWeightedBilin w (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap)
      (typeAFiniteGenerator q hq hD n L i 0) T := by
  apply finiteWeightedAdjoint_of_basis (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
  intro x y
  by_cases hx : 0<x.val i.succ
  · rw [typeAFiniteGenerator_E_raised q hq hD n L x i hx,finiteWeightedPair_smul_left]
    by_cases hy : 0<y.val i.castSucc
    · let z := loweredOccupation n L y i hy
      have hz := loweredOccupation_source_positive n L y i hy
      have hyz := raised_loweredOccupation n L y i hy
      change raisedOccupation n L z i hz=y at hyz
      rw [← hyz,hT z hz,finiteWeightedPair_smul_right,finiteWeightedPair_basis,finiteWeightedPair_basis]
      by_cases hzx : x=z
      · simpa only [← hzx,ite_true] using hstep x hx
      · have hxy : raisedOccupation n L x i hx≠raisedOccupation n L z i hz :=
          fun he => hzx (raisedOccupation_injective n L i x z hx hz he)
        rw [if_neg hxy,if_neg hzx,mul_zero,mul_zero]
    · have hy0 : y.val i.castSucc=0 := by have hnonneg := y.property.1 i.castSucc;omega
      rw [hT0 y hy0,finiteWeightedPair_basis]
      have hxy : raisedOccupation n L x i hx≠y := by
        intro he
        have htarget := raisedOccupation_target n L x i hx
        rw [he,hy0] at htarget
        have hnonneg := x.property.1 i.castSucc
        omega
      rw [if_neg hxy,mul_zero]
      simp [finiteWeightedPair]
  · have hx0 : x.val i.succ=0 := by have hnonneg := x.property.1 i.succ;omega
    rw [typeAFiniteGenerator_E_zero q hq hD n L x i hx0]
    by_cases hy : 0<y.val i.castSucc
    · let z := loweredOccupation n L y i hy
      have hz := loweredOccupation_source_positive n L y i hy
      have hyz := raised_loweredOccupation n L y i hy
      change raisedOccupation n L z i hz=y at hyz
      rw [← hyz,hT z hz,finiteWeightedPair_smul_right,finiteWeightedPair_basis]
      have hxz : x≠z := by
        intro he
        have hz' : 0<z.val i.succ := hz
        rw [← he,hx0] at hz'
        omega
      rw [if_neg hxz,mul_zero]
      simp [finiteWeightedPair]
    · have hy0 : y.val i.castSucc=0 := by have hnonneg := y.property.1 i.castSucc;omega
      rw [hT0 y hy0]
      simp [finiteWeightedPair]

end AMSPhysical
#print axioms AMSPhysical.occupation_E_adjoint_of_edges
