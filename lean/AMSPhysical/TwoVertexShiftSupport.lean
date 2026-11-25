import TwoVertexProjection
import QuantumOccupationShifts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical

theorem twoVertexOccupation_of_support (n : ℕ) (hn : 0<n) (L : ℕ)
    (x : occupationWeights (Fin (n+1)) L)
    (h : ∀ j : Fin (n+1),j≠0 → j≠secondVertex n hn → x.val j=0) :
    ∃ k : Fin (L+1),x=twoVertexOccupation n hn L k := by
  classical
  have he : (∑ j : Fin (n+1),x.val j)=x.val 0+x.val (secondVertex n hn) := by
    calc
      _=∑ j∈({0,secondVertex n hn}:Finset (Fin (n+1))),x.val j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j hj hjnot
        apply h
        · intro hz
          exact hjnot (by simp [hz])
        · intro hz
          exact hjnot (by simp [hz])
      _=_ := by simp [secondVertex_ne_zero n hn,Ne.symm (secondVertex_ne_zero n hn)]
  have hs:=x.property.2
  rw [he] at hs
  have hx0:=x.property.1 (0:Fin (n+1))
  have hx1:=x.property.1 (secondVertex n hn)
  let k : Fin (L+1):=⟨(x.val (secondVertex n hn)).toNat,by omega⟩
  refine ⟨k,?_⟩
  apply Subtype.ext
  funext j
  by_cases hj0:j=0
  · subst j
    rw [twoVertexOccupation_first]
    dsimp only [k]
    omega
  · by_cases hj1:j=secondVertex n hn
    · subst j
      rw [twoVertexOccupation_second]
      exact (Int.toNat_of_nonneg hx1).symm
    · rw [h j hj0 hj1,twoVertexOccupation_other n hn L k j hj0 hj1]

theorem twoVertexProjection_basis_outside (n : ℕ) (hn : 0<n) (L : ℕ)
    (x : occupationWeights (Fin (n+1)) L)
    (h : ¬∃ k : Fin (L+1),x=twoVertexOccupation n hn L k) :
    twoVertexProjection n hn L (quantumOccupationBasis (K:=ℝ) L x)=0 := by
  apply (standardWeightBasis (K:=ℝ) L).equivFun.injective
  funext k
  rw [twoVertexProjection_coordinate]
  simp only [Module.Basis.equivFun_apply,Module.Basis.repr_self,Finsupp.single_apply,map_zero,Pi.zero_apply]
  exact if_neg (fun he =>h ⟨k,he⟩)

/-- Adding nonnegative occupation cannot return an off-boundary basis
vector to the literal first-two-coordinate boundary. -/
theorem shiftedOccupation_outside_twoVertex (n : ℕ) (hn : 0<n) (L A : ℕ)
    (x : occupationWeights (Fin (n+1)) L)
    (hx : ¬∃ k : Fin (L+1),x=twoVertexOccupation n hn L k) (j : Fin (n+1)) :
    ¬∃ k : Fin (L+A+1),shiftedOccupation n L A j x=twoVertexOccupation n hn (L+A) k := by
  rintro ⟨k,hk⟩
  apply hx
  apply twoVertexOccupation_of_support n hn L x
  intro i hi0 hi1
  have he:=congrArg (fun z : occupationWeights (Fin (n+1)) (L+A) =>z.val i) hk
  dsimp only at he
  rw [twoVertexOccupation_other n hn (L+A) k i hi0 hi1] at he
  change x.val i+(Pi.single j (A:ℤ):Fin (n+1) → ℤ) i=0 at he
  have hp:=x.property.1 i
  simp only [Pi.single_apply] at he
  split_ifs at he <;> omega

end AMSPhysical
#print axioms AMSPhysical.shiftedOccupation_outside_twoVertex
