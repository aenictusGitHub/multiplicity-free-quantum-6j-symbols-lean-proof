import QuantumTypeAPivotal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem typeAInversePivot_eigen (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (v : V) (w : Fin n → ℤ)
    (hw : ∀ i,ρ (typeAAlgebraGenerator q n i 3) v=q^(w i) • v) :
    ρ (typeAInversePivot q n) v=q^(∑ i : Fin n,(typeAPivotalExponent n i : ℤ)*w i) • v := by
  unfold typeAInversePivot
  rw [map_list_prod,List.map_ofFn]
  change (List.ofFn (fun i : Fin n =>ρ ((typeAAlgebraGenerator q n i 3)^(typeAPivotalExponent n i)))).prod v=_
  simp only [map_pow]
  rw [linearEnd_ofFn_prod_eigen n _ (fun i =>(q^(w i))^(typeAPivotalExponent n i)) v
    (fun i =>linearEnd_pow_eigen _ _ _ (hw i) _)]
  congr 1
  rw [zpow_finset_sum q hq]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← zpow_natCast (q^(w i)),← zpow_mul]
  congr 1
  ring

end AMSPhysical
