import QuantumOccupationGraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def mixedBoundaryOccupation (n m r : ℕ) (hr : r≤m) : occupationWeights (Fin (n+1)) m :=
  ⟨Pi.single 0 (r:ℤ)+Pi.single (Fin.last n) ((m-r:ℕ):ℤ),by
    constructor
    · intro k
      simp only [Pi.add_apply,Pi.single_apply]
      split_ifs <;> omega
    · simp only [Pi.add_apply,Finset.sum_add_distrib]
      simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      omega⟩

theorem mixedBoundaryOccupation_first (n m r : ℕ) (hn : 0<n) (hr : r≤m) :
    (mixedBoundaryOccupation n m r hr).val 0=(r:ℤ) := by
  have hne : (Fin.last n : Fin (n+1))≠0 := by intro h;have he := congrArg Fin.val h;simp only [Fin.val_last,Fin.val_zero] at he;omega
  simp [mixedBoundaryOccupation,Pi.single_apply,hne]

theorem mixedBoundaryOccupation_injective (n m : ℕ) (hn : 0<n) (r s : ℕ) (hr : r≤m) (hs : s≤m)
    (he : mixedBoundaryOccupation n m r hr=mixedBoundaryOccupation n m s hs) : r=s := by
  have h := congrArg (fun z : occupationWeights (Fin (n+1)) m => z.val 0) he
  dsimp only at h
  rw [mixedBoundaryOccupation_first n m r hn hr,mixedBoundaryOccupation_first n m s hn hs] at h
  exact_mod_cast h

theorem occupation_endpoints_reconstruction (n m : ℕ) (hn : 0<n)
    (y : occupationWeights (Fin (n+1)) m)
    (hInterior : ∀ k : Fin (n+1),k≠0 → k≠Fin.last n → y.val k=0) :
    y=mixedBoundaryOccupation n m (y.val 0).toNat (by have h₀:=y.property.1 0;have h₁:=occupationWeight_bound m y 0;omega) := by
  have hne : (Fin.last n : Fin (n+1))≠0 := by intro h;have he := congrArg Fin.val h;simp only [Fin.val_last,Fin.val_zero] at he;omega
  have hy0 : ((y.val 0).toNat:ℤ)=y.val 0 := Int.toNat_of_nonneg (y.property.1 0)
  have hShape : y.val=Pi.single 0 (y.val 0)+Pi.single (Fin.last n) (y.val (Fin.last n)) := by
    funext k
    by_cases hk : k=0
    · subst k
      simp [Pi.single_apply,hne]
    · by_cases hkn : k=Fin.last n
      · subst k
        simp [Pi.single_apply,hne,Ne.symm hne]
      · simp [Pi.single_apply,hk,Ne.symm hk,hkn,Ne.symm hkn,hInterior k hk hkn]
  have hSum : y.val 0+y.val (Fin.last n)=(m:ℤ) := by
    have h := y.property.2
    rw [hShape] at h
    simpa [Pi.add_apply,Finset.sum_add_distrib,Pi.single_apply] using h
  apply Subtype.ext
  change y.val=
    Pi.single 0 (((y.val 0).toNat:ℕ):ℤ)+Pi.single (Fin.last n) ((m-(y.val 0).toNat:ℕ):ℤ)
  conv_lhs => rw [hShape]
  congr 1
  · rw [hy0]
  · have hb := occupationWeight_bound m y 0
    congr 1
    omega

end AMSPhysical
