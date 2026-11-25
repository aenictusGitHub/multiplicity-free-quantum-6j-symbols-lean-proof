import QuantumOccupationEnergy

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def secondVertex (n : ℕ) (hn : 0<n) : Fin (n+1) := ⟨1,by omega⟩

theorem secondVertex_ne_zero (n : ℕ) (hn : 0<n) : secondVertex n hn≠0 := by
  intro h
  have he := congrArg Fin.val h
  change (1:ℕ)=0 at he
  omega

def twoVertexOccupation (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) : occupationWeights (Fin (n+1)) L :=
  ⟨Pi.single 0 ((L-k.val:ℕ):ℤ)+Pi.single (secondVertex n hn) (k.val:ℤ),by
    constructor
    · intro j
      simp only [Pi.add_apply,Pi.single_apply]
      split_ifs <;> omega
    · simp only [Pi.add_apply,Finset.sum_add_distrib]
      simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      have hk:=k.isLt
      omega⟩

theorem twoVertexOccupation_first (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    (twoVertexOccupation n hn L k).val 0=((L-k.val:ℕ):ℤ) := by
  simp [twoVertexOccupation,Pi.single_apply,secondVertex_ne_zero n hn]

theorem twoVertexOccupation_second (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    (twoVertexOccupation n hn L k).val (secondVertex n hn)=(k.val:ℤ) := by
  simp [twoVertexOccupation,Pi.single_apply,secondVertex_ne_zero n hn,Ne.symm (secondVertex_ne_zero n hn)]

theorem twoVertexOccupation_other (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1))
    (j : Fin (n+1)) (hj0 : j≠0) (hj1 : j≠secondVertex n hn) :
    (twoVertexOccupation n hn L k).val j=0 := by
  simp [twoVertexOccupation,Pi.single_apply,hj0,Ne.symm hj0,hj1,Ne.symm hj1]

theorem twoVertexOccupation_injective (n : ℕ) (hn : 0<n) (L : ℕ) :
    Function.Injective (twoVertexOccupation n hn L) := by
  intro i j h
  have he := congrArg (fun t : occupationWeights (Fin (n+1)) L => t.val (secondVertex n hn)) h
  dsimp only at he
  rw [twoVertexOccupation_second,twoVertexOccupation_second] at he
  apply Fin.ext
  exact_mod_cast he

theorem twoVertexOccupation_zero (n : ℕ) (hn : 0<n) (L : ℕ) :
    twoVertexOccupation n hn L 0=highestOccupation n L := by
  apply Subtype.ext
  simp only [twoVertexOccupation,highestOccupation,Fin.val_zero,Nat.sub_zero,Nat.cast_zero,Pi.single_zero,add_zero]

theorem twoVertexOccupation_simple (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    simpleOccupationWeight n (twoVertexOccupation n hn L k).val (⟨0,hn⟩ : Fin n)=(L:ℤ)-2*k.val := by
  change (twoVertexOccupation n hn L k).val 0-(twoVertexOccupation n hn L k).val (secondVertex n hn)=_
  rw [twoVertexOccupation_first,twoVertexOccupation_second]
  have hk:=k.isLt
  omega

theorem twoVertexOccupation_raised_succ (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin L)
    (hi : 0<(twoVertexOccupation n hn L k.succ).val (secondVertex n hn)) :
    raisedOccupation n L (twoVertexOccupation n hn L k.succ) (⟨0,hn⟩ : Fin n) hi=
      twoVertexOccupation n hn L k.castSucc := by
  apply Subtype.ext
  funext j
  by_cases hj0 : j=0
  · subst j
    change (twoVertexOccupation n hn L k.succ).val 0+1=(twoVertexOccupation n hn L k.castSucc).val 0
    rw [twoVertexOccupation_first,twoVertexOccupation_first]
    have hk:=k.isLt
    simp only [Fin.val_succ,Fin.coe_castSucc]
    omega
  · by_cases hj1 : j=secondVertex n hn
    · subst j
      change (twoVertexOccupation n hn L k.succ).val (secondVertex n hn)-1=
        (twoVertexOccupation n hn L k.castSucc).val (secondVertex n hn)
      rw [twoVertexOccupation_second,twoVertexOccupation_second]
      simp only [Fin.val_succ,Fin.coe_castSucc,Nat.cast_add,Nat.cast_one]
      ring
    · change (twoVertexOccupation n hn L k.succ).val j+latticeRoot (0:Fin (n+1)) (secondVertex n hn) j=
        (twoVertexOccupation n hn L k.castSucc).val j
      rw [twoVertexOccupation_other n hn L k.succ j hj0 hj1,
        twoVertexOccupation_other n hn L k.castSucc j hj0 hj1,latticeRoot_other _ _ _ hj0 hj1]
      rfl

end AMSPhysical
