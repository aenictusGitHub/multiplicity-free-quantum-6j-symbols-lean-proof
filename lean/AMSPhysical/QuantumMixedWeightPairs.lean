import QuantumMixedWeight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem simpleWeight_fixed_sum_injective (n : ℕ) (x y : Fin (n+1) → ℤ)
    (hs : (∑ k,x k)=∑ k,y k) (he : simpleOccupationWeight n x=simpleOccupationWeight n y) : x=y := by
  have hc : ∀ k : Fin (n+1),x k-y k=x 0-y 0 := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hh := congrFun he i
      change x i.castSucc-x i.succ=y i.castSucc-y i.succ at hh
      omega
  have hz : (∑ k : Fin (n+1),(x k-y k))=0 := by rw [Finset.sum_sub_distrib,hs,sub_self]
  have hsum : (∑ k : Fin (n+1),(x k-y k))=∑ _k : Fin (n+1),(x 0-y 0) :=
    Finset.sum_congr rfl (fun k _ => hc k)
  rw [hz] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hN : ((n+1:ℕ):ℤ)≠0 := by omega
  have hzero : x 0-y 0=0 := (mul_eq_zero.mp hsum.symm).resolve_left hN
  funext k
  have hh := hc k
  omega

def mixedHighestDifference (n a b : ℕ) : Fin (n+1) → ℤ :=
  Pi.single 0 (a:ℤ)-Pi.single (Fin.last n) (b:ℤ)

theorem mixedHighestDifference_sum (n a b : ℕ) : (∑ k,mixedHighestDifference n a b k)=(a:ℤ)-b := by
  simp [mixedHighestDifference,Finset.sum_sub_distrib]

theorem mixedHighestDifference_simple (n a b : ℕ) :
    simpleOccupationWeight n (mixedHighestDifference n a b)=mixedHighestDynkin n a b := by
  funext i
  have hi0 : i.succ≠(0:Fin (n+1)) := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ,Fin.val_zero] at hh
    omega
  have hin : i.castSucc≠Fin.last n := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.coe_castSucc,Fin.val_last] at hh
    exact (Nat.ne_of_lt i.isLt) hh
  simp only [simpleOccupationWeight,mixedHighestDifference,mixedHighestDynkin,Pi.sub_apply,Pi.single_apply]
  simp only [if_neg hi0,if_neg (Ne.symm hi0),if_neg hin,if_neg (Ne.symm hin)]
  split_ifs <;> ring

theorem mixedWeight_pair_difference (n r a b : ℕ)
    (x : occupationWeights (Fin (n+1)) (r+a)) (y : occupationWeights (Fin (n+1)) (r+b))
    (he : ∀ i : Fin n,simpleOccupationWeight n x.val i-simpleOccupationWeight n y.val i=mixedHighestDynkin n a b i) :
    x.val-y.val=mixedHighestDifference n a b := by
  apply simpleWeight_fixed_sum_injective n
  · simp only [Pi.sub_apply,Finset.sum_sub_distrib,x.property.2,y.property.2,mixedHighestDifference_sum]
    push_cast
    ring
  · rw [mixedHighestDifference_simple]
    funext i
    have hh := he i
    change (x.val i.castSucc-y.val i.castSucc)-(x.val i.succ-y.val i.succ)=_
    unfold simpleOccupationWeight at hh
    omega

/-- Every tensor basis pair of the required highest weight has a unique
common contraction occupation. No extra candidate-only support is assumed. -/
theorem mixedWeight_pair_reconstruction (n r a b : ℕ) (hn : 0<n)
    (x : occupationWeights (Fin (n+1)) (r+a)) (y : occupationWeights (Fin (n+1)) (r+b))
    (he : ∀ i : Fin n,simpleOccupationWeight n x.val i-simpleOccupationWeight n y.val i=mixedHighestDynkin n a b i) :
    ∃ t : occupationWeights (Fin (n+1)) r,shiftedOccupation n r a 0 t=x ∧
      shiftedOccupation n r b (Fin.last n) t=y := by
  classical
  have hd := mixedWeight_pair_difference n r a b x y he
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_last,Fin.val_zero] at hh
    omega
  let z : Fin (n+1) → ℤ := x.val-Pi.single 0 (a:ℤ)
  have hz : z∈occupationWeights (Fin (n+1)) r := by
    constructor
    · intro k
      by_cases hk : k=0
      · subst k
        have h0 := congrFun hd 0
        simp only [Pi.sub_apply,mixedHighestDifference,Pi.single_apply,ite_true,if_neg hn0] at h0
        have hy := y.property.1 0
        change 0≤x.val 0-a
        omega
      · change 0≤x.val k-(Pi.single 0 (a:ℤ) : Fin (n+1) → ℤ) k
        simpa [Pi.single_apply,hk,Ne.symm hk] using x.property.1 k
    · change (∑ k,(x.val k-(Pi.single 0 (a:ℤ) : Fin (n+1) → ℤ) k))=(r:ℤ)
      rw [Finset.sum_sub_distrib,x.property.2]
      simp
  refine ⟨⟨z,hz⟩,?_,?_⟩
  · apply Subtype.ext
    change (x.val-Pi.single 0 (a:ℤ))+Pi.single 0 (a:ℤ)=x.val
    abel
  · apply Subtype.ext
    change (x.val-Pi.single 0 (a:ℤ))+Pi.single (Fin.last n) (b:ℤ)=y.val
    have hh : x.val-y.val=Pi.single 0 (a:ℤ)-Pi.single (Fin.last n) (b:ℤ) := hd
    linear_combination hh

end AMSPhysical
#print axioms AMSPhysical.mixedWeight_pair_reconstruction
