import QuantumLatticeSerre

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def typeACartan (n : ℕ) (i j : Fin n) : ℤ :=
  if i=j then 2 else if i.val+1=j.val ∨ j.val+1=i.val then -1 else 0

def typeARoot (n : ℕ) (i : Fin n) : Fin (n+1) → ℤ := latticeRoot i.castSucc i.succ

def typeAQuantumE (q : K) (n : ℕ) (i : Fin n) : Module.End K (QuantumLatticeSpace K (Fin (n+1))) :=
  quantumLatticeMove q i.castSucc i.succ
def typeAQuantumF (q : K) (n : ℕ) (i : Fin n) : Module.End K (QuantumLatticeSpace K (Fin (n+1))) :=
  quantumLatticeMove q i.succ i.castSucc
def typeAQuantumK (q : K) (n : ℕ) (i : Fin n) : Module.End K (QuantumLatticeSpace K (Fin (n+1))) :=
  quantumLatticeCartan q (typeARoot n i)
def typeAQuantumKi (q : K) (n : ℕ) (i : Fin n) : Module.End K (QuantumLatticeSpace K (Fin (n+1))) :=
  quantumLatticeCartan q (-typeARoot n i)

theorem typeA_root_endpoints (n : ℕ) (i : Fin n) : i.castSucc≠i.succ := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.coe_castSucc,Fin.val_succ] at hh
  omega

theorem typeA_cartan_entry (n : ℕ) (i j : Fin n) :
    typeARoot n i j.castSucc-typeARoot n i j.succ=typeACartan n i j := by
  unfold typeARoot latticeRoot typeACartan
  simp only [Pi.sub_apply,Pi.single_apply,Fin.ext_iff,Fin.coe_castSucc,Fin.val_succ]
  split_ifs <;> omega

theorem typeA_K_inverse (q : K) (hq : q≠0) (n : ℕ) (i : Fin n) :
    typeAQuantumK q n i*typeAQuantumKi q n i=1 := quantumLatticeCartan_inverse q hq _

theorem typeA_Ki_inverse (q : K) (hq : q≠0) (n : ℕ) (i : Fin n) :
    typeAQuantumKi q n i*typeAQuantumK q n i=1 := by
  simpa only [neg_neg] using quantumLatticeCartan_inverse q hq (-typeARoot n i)

theorem typeA_K_commute (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    typeAQuantumK q n i*typeAQuantumK q n j=typeAQuantumK q n j*typeAQuantumK q n i := by
  unfold typeAQuantumK
  rw [quantumLatticeCartan_mul q hq,quantumLatticeCartan_mul q hq]
  congr 1
  abel

theorem typeA_K_E (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    typeAQuantumK q n i*typeAQuantumE q n j=q^(typeACartan n i j) • (typeAQuantumE q n j*typeAQuantumK q n i) := by
  simpa only [typeAQuantumK,typeAQuantumE,typeA_cartan_entry] using
    quantumLatticeCartan_move q hq (typeARoot n i) j.castSucc j.succ

theorem typeA_K_F (q : K) (hq : q≠0) (n : ℕ) (i j : Fin n) :
    typeAQuantumK q n i*typeAQuantumF q n j=q^(-typeACartan n i j) • (typeAQuantumF q n j*typeAQuantumK q n i) := by
  have he : typeARoot n i j.succ-typeARoot n i j.castSucc= -typeACartan n i j := by
    linear_combination -(typeA_cartan_entry n i j)
  simpa only [typeAQuantumK,typeAQuantumF,he] using
    quantumLatticeCartan_move q hq (typeARoot n i) j.succ j.castSucc

theorem typeA_EF_same (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (i : Fin n) :
    typeAQuantumE q n i*typeAQuantumF q n i-typeAQuantumF q n i*typeAQuantumE q n i=
      (q-q⁻¹)⁻¹ • (typeAQuantumK q n i-typeAQuantumKi q n i) :=
  quantumLatticeMove_commutator q hq hD i.castSucc i.succ (typeA_root_endpoints n i)

theorem typeA_EF_different (q : K) (n : ℕ) (i j : Fin n) (hij : i≠j) :
    typeAQuantumE q n i*typeAQuantumF q n j=typeAQuantumF q n j*typeAQuantumE q n i := by
  have hstart : j.castSucc≠i.castSucc := by
    intro h
    apply hij
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [Fin.coe_castSucc] at hh
    omega
  have hend : i.succ≠j.succ := by
    intro h
    apply hij
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [Fin.val_succ] at hh
    omega
  exact quantumLatticeMove_commute q i.castSucc i.succ j.succ j.castSucc
    (typeA_root_endpoints n i) (Ne.symm (typeA_root_endpoints n j)) hend hstart

theorem typeA_E_distant (q : K) (n : ℕ) (i j : Fin n)
    (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
    typeAQuantumE q n i*typeAQuantumE q n j=typeAQuantumE q n j*typeAQuantumE q n i := by
  apply quantumLatticeMove_commute q i.castSucc i.succ j.castSucc j.succ
    (typeA_root_endpoints n i) (typeA_root_endpoints n j)
  · intro he
    have hh := congrArg Fin.val he
    simp only [Fin.coe_castSucc,Fin.val_succ] at hh
    omega
  · intro he
    have hh := congrArg Fin.val he
    simp only [Fin.coe_castSucc,Fin.val_succ] at hh
    omega

theorem typeA_F_distant (q : K) (n : ℕ) (i j : Fin n)
    (hd : i.val+1 < j.val ∨ j.val+1 < i.val) :
    typeAQuantumF q n i*typeAQuantumF q n j=typeAQuantumF q n j*typeAQuantumF q n i := by
  apply quantumLatticeMove_commute q i.succ i.castSucc j.succ j.castSucc
    (Ne.symm (typeA_root_endpoints n i)) (Ne.symm (typeA_root_endpoints n j))
  · intro he
    have hh := congrArg Fin.val he
    simp only [Fin.coe_castSucc,Fin.val_succ] at hh
    omega
  · intro he
    have hh := congrArg Fin.val he
    simp only [Fin.coe_castSucc,Fin.val_succ] at hh
    omega

end AMSPhysical

#print axioms AMSPhysical.typeA_EF_same
#print axioms AMSPhysical.typeA_K_E
