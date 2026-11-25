import QuantumTypeARoots

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

theorem typeA_adjacent_vertices (n : ℕ) (i j : Fin n) (hij : i.val+1=j.val) :
    j.castSucc=i.succ ∧ i.castSucc≠j.succ ∧ i.succ≠j.succ := by
  constructor
  · apply Fin.ext
    simp only [Fin.coe_castSucc,Fin.val_succ]
    omega
  · constructor
    · intro he
      have hh := congrArg Fin.val he
      simp only [Fin.coe_castSucc,Fin.val_succ] at hh
      omega
    · intro he
      have hh := congrArg Fin.val he
      simp only [Fin.val_succ] at hh
      omega

theorem typeA_E_serre_left (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ)
    (i j : Fin n) (hij : i.val+1=j.val) :
    typeAQuantumE q n i*typeAQuantumE q n i*typeAQuantumE q n j-
      (q+q⁻¹) • (typeAQuantumE q n i*typeAQuantumE q n j*typeAQuantumE q n i)+
      typeAQuantumE q n j*typeAQuantumE q n i*typeAQuantumE q n i=0 := by
  obtain ⟨hv,hik,hjk⟩ := typeA_adjacent_vertices n i j hij
  simpa only [typeAQuantumE,hv] using quantumLatticeMove_serre_left q hq hD
    i.castSucc i.succ j.succ (typeA_root_endpoints n i) hjk hik

theorem typeA_E_serre_right (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ)
    (i j : Fin n) (hij : i.val+1=j.val) :
    typeAQuantumE q n j*typeAQuantumE q n j*typeAQuantumE q n i-
      (q+q⁻¹) • (typeAQuantumE q n j*typeAQuantumE q n i*typeAQuantumE q n j)+
      typeAQuantumE q n i*typeAQuantumE q n j*typeAQuantumE q n j=0 := by
  obtain ⟨hv,hik,hjk⟩ := typeA_adjacent_vertices n i j hij
  simpa only [typeAQuantumE,hv] using quantumLatticeMove_serre_right q hq hD
    i.castSucc i.succ j.succ hjk hik

theorem typeA_F_serre_left (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ)
    (i j : Fin n) (hij : i.val+1=j.val) :
    typeAQuantumF q n i*typeAQuantumF q n i*typeAQuantumF q n j-
      (q+q⁻¹) • (typeAQuantumF q n i*typeAQuantumF q n j*typeAQuantumF q n i)+
      typeAQuantumF q n j*typeAQuantumF q n i*typeAQuantumF q n i=0 := by
  obtain ⟨hv,hik,hjk⟩ := typeA_adjacent_vertices n i j hij
  simpa only [typeAQuantumF,hv] using quantumLatticeMove_serre_right q hq hD
    j.succ i.succ i.castSucc (Ne.symm (typeA_root_endpoints n i)) (Ne.symm hik)

theorem typeA_F_serre_right (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ)
    (i j : Fin n) (hij : i.val+1=j.val) :
    typeAQuantumF q n j*typeAQuantumF q n j*typeAQuantumF q n i-
      (q+q⁻¹) • (typeAQuantumF q n j*typeAQuantumF q n i*typeAQuantumF q n j)+
      typeAQuantumF q n i*typeAQuantumF q n j*typeAQuantumF q n j=0 := by
  obtain ⟨hv,hik,hjk⟩ := typeA_adjacent_vertices n i j hij
  simpa only [typeAQuantumF,hv] using quantumLatticeMove_serre_left q hq hD
    j.succ i.succ i.castSucc (Ne.symm hjk) (Ne.symm (typeA_root_endpoints n i)) (Ne.symm hik)

end AMSPhysical

#print axioms AMSPhysical.typeA_E_serre_left
#print axioms AMSPhysical.typeA_F_serre_left
