import QuantumMixedNormSlots

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem mixedNormSlot_product (q : ℝ) (a b n : ℕ) (hn : 0<n) :
    (∏ k : Fin (n+1),mixedNormSlot q a b n k)=
      PowerSeries.C (qfactorial q a*qfactorial q b)*mixedNormGeneratingSeries q a b n := by
  classical
  cases n with
  | zero => omega
  | succ N =>
    have hlast : (Fin.last (N+1) : Fin (N+1+1))≠0 := by
      intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_last,Fin.val_zero] at hh
      omega
    have hi (i : Fin N) : mixedNormSlot q a b (N+1) i.castSucc.succ=
        geometricSeries ((q^2)^(-((i.val+1:ℕ):ℤ))) := by
      have hi0 : i.castSucc.succ≠(0:Fin (N+1+1)) := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_succ,Fin.coe_castSucc,Fin.val_zero] at hh
        omega
      have hin : i.castSucc.succ≠Fin.last (N+1) := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_succ,Fin.coe_castSucc,Fin.val_last] at hh
        have hn' := i.isLt
        omega
      simp only [mixedNormSlot,if_neg hi0,if_neg hin,Fin.val_succ,Fin.coe_castSucc]
    rw [Fin.prod_univ_succ,Fin.prod_univ_castSucc]
    have h0 : mixedNormSlot q a b (N+1) 0=PowerSeries.C (qfactorial q a)*gaussianSeries (q^2) a := by
      simp only [mixedNormSlot,if_pos rfl,ite_true]
    have hL : mixedNormSlot q a b (N+1) (Fin.last N).succ=PowerSeries.C (qfactorial q b)*
        PowerSeries.rescale ((q^2)^(-((N+1+b:ℕ):ℤ))) (gaussianSeries (q^2) b) := by
      have he : (Fin.last N).succ=Fin.last (N+1) := by apply Fin.ext;rfl
      rw [he]
      simp only [mixedNormSlot,if_neg hlast,if_pos rfl,ite_true]
    rw [h0,hL]
    have hI : (∏ i : Fin N,mixedNormSlot q a b (N+1) i.castSucc.succ)=
        geometricBlock (q^2) (-(N:ℤ)) N := by
      simp only [hi]
      calc
        _ = ∏ k∈Finset.range N,geometricSeries ((q^2)^(-((k+1:ℕ):ℤ))) :=
          Fin.prod_univ_eq_prod_range (fun k : ℕ => geometricSeries ((q^2)^(-((k+1:ℕ):ℤ)))) N
        _ = _ := geometricBlock_negative (q^2) N
    rw [hI]
    unfold mixedNormGeneratingSeries
    rw [show N+1-1=N by omega,map_mul]
    ring

end AMSPhysical
#print axioms AMSPhysical.mixedNormSlot_product
