import TwoVertexOccupation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem occupation_twoVertex_reconstruction (n : ℕ) (hn : 0<n) (m : ℕ)
    (y : occupationWeights (Fin (n+1)) m)
    (hInterior : ∀ k : Fin (n+1),k≠0 → k≠secondVertex n hn → y.val k=0) :
    y=twoVertexOccupation n hn m
      ⟨(y.val (secondVertex n hn)).toNat,by
        have h0:=y.property.1 (secondVertex n hn)
        have h1:=occupationWeight_bound m y (secondVertex n hn)
        omega⟩ := by
  let r := (y.val (secondVertex n hn)).toNat
  have hr : (r:ℤ)=y.val (secondVertex n hn) := Int.toNat_of_nonneg (y.property.1 _)
  have hShape : y.val=Pi.single 0 (y.val 0)+Pi.single (secondVertex n hn) (y.val (secondVertex n hn)) := by
    funext k
    by_cases hk0 : k=0
    · subst k
      simp [Pi.single_apply,secondVertex_ne_zero n hn]
    · by_cases hk1 : k=secondVertex n hn
      · subst k
        simp [Pi.single_apply,secondVertex_ne_zero n hn,Ne.symm (secondVertex_ne_zero n hn)]
      · simp [Pi.single_apply,hk0,Ne.symm hk0,hk1,Ne.symm hk1,hInterior k hk0 hk1]
  have hSum : y.val 0+y.val (secondVertex n hn)=(m:ℤ) := by
    have h:=y.property.2
    rw [hShape] at h
    simpa [Pi.add_apply,Finset.sum_add_distrib,Pi.single_apply] using h
  have hFirst : y.val 0=((m-r:ℕ):ℤ) := by
    have h0:=y.property.1 (secondVertex n hn)
    have h1:=occupationWeight_bound m y (secondVertex n hn)
    omega
  apply Subtype.ext
  change y.val=(Pi.single 0 ((m-r:ℕ):ℤ)+Pi.single (secondVertex n hn) (r:ℤ) : Fin (n+1) → ℤ)
  calc
    _ = (Pi.single 0 (y.val 0)+Pi.single (secondVertex n hn) (y.val (secondVertex n hn)) : Fin (n+1) → ℤ) := hShape
    _ = _ := by rw [hFirst,← hr]

end AMSPhysical
