import QuantumCasimirBaseSpectrum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem representation_K_F (q : K) (ρ : UqSL2 q →ₐ[K] Module.End K V) (v : V) :
    ρ (uqGenerator q 2) (ρ (uqGenerator q 1) v)=
      q^(-2:ℤ) • ρ (uqGenerator q 1) (ρ (uqGenerator q 2) v) := by
  have h := congrArg ρ (uq_weightF q)
  simp only [map_mul,map_smul] at h
  simpa only [Module.End.mul_apply,LinearMap.smul_apply] using
    congrArg (fun T : Module.End K V => T v) h

theorem representation_E_F_weight (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (L : ℤ) (v : V)
    (hK : ρ (uqGenerator q 2) v=q^L • v) :
    ρ (uqGenerator q 0) (ρ (uqGenerator q 1) v)=
      ρ (uqGenerator q 1) (ρ (uqGenerator q 0) v)+qInteger q L • v := by
  have hKi := representation_Kinv_eigen q ρ (q^L) (zpow_ne_zero _ hq) v hK
  have h := congrArg ρ (uq_commutator q)
  simp only [map_mul,map_sub,map_smul] at h
  have he := congrArg (fun T : Module.End K V => T v) h
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.smul_apply,hK,hKi,
    ← sub_smul,smul_smul] at he
  have hc : (q-q⁻¹)⁻¹*(q^L-(q^L)⁻¹)=qInteger q L := by
    simp only [qInteger,zpow_neg,div_eq_mul_inv,mul_comm]
  rw [hc] at he
  exact (sub_eq_iff_eq_add').mp he

theorem representation_K_Fpow (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (L : ℤ) (v : V)
    (hK : ρ (uqGenerator q 2) v=q^L • v) (k : ℕ) :
    ρ (uqGenerator q 2) (((ρ (uqGenerator q 1))^k) v)=
      q^(L-2*k) • (((ρ (uqGenerator q 1))^k) v) := by
  induction k with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.cast_zero,mul_zero,sub_zero] using hK
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,representation_K_F,ih,map_smul,smul_smul,← zpow_add₀ hq]
    have hi : (-2:ℤ)+(L-2*k)=L-2*(k+1:ℕ) := by omega
    rw [hi]

theorem representation_E_Fpow_succ (q : K) (hq : q≠0) (hd : q-q⁻¹≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (L : ℤ) (v : V)
    (hE : ρ (uqGenerator q 0) v=0) (hK : ρ (uqGenerator q 2) v=q^L • v) (k : ℕ) :
    ρ (uqGenerator q 0) (((ρ (uqGenerator q 1))^(k+1)) v)=
      (qInteger q (k+1:ℕ)*qInteger q (L-k)) • (((ρ (uqGenerator q 1))^k) v) := by
  induction k with
  | zero =>
    simp only [Nat.zero_add,pow_one,pow_zero,Module.End.one_apply,Nat.cast_zero,Nat.cast_one,sub_zero]
    rw [representation_E_F_weight q hq ρ L v hK,hE,map_zero,zero_add,qInteger_one q hd,one_mul]
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,
      representation_E_F_weight q hq ρ (L-2*(k+1:ℕ)) _ (representation_K_Fpow q hq ρ L v hK (k+1)),
      ih,map_smul]
    have hF : ρ (uqGenerator q 1) (((ρ (uqGenerator q 1))^k) v)=
        ((ρ (uqGenerator q 1))^(k+1)) v := by rw [pow_succ',Module.End.mul_apply]
    rw [hF,← add_smul]
    have hc := qInteger_cross q hq hd (k+1:ℕ) (L-(k+1:ℕ))
    have h₁ : L-(k+1:ℕ)+1=L-k := by omega
    have h₂ : L-(k+1:ℕ)-(k+1:ℕ)=L-2*(k+1:ℕ) := by omega
    rw [h₁,h₂] at hc
    have hcoef : qInteger q (k+1:ℕ)*qInteger q (L-k)+qInteger q (L-2*(k+1:ℕ))=
        qInteger q (k+1+1:ℕ)*qInteger q (L-(k+1:ℕ)) := by
      norm_cast at hc ⊢
      linear_combination -hc
    rw [hcoef]

/-- Every lowering string up to its highest weight is nonzero. -/
theorem representation_Fpow_ne_zero (q : K) (hq : q≠0) (hd : q-q⁻¹≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (L : ℕ) (v : V) (hv : v≠0)
    (hE : ρ (uqGenerator q 0) v=0) (hK : ρ (uqGenerator q 2) v=q^(L:ℤ) • v)
    (hqi : ∀ j : ℤ,0<j → j≤(L:ℤ) → qInteger q j≠0) (k : ℕ) (hk : k≤L) :
    ((ρ (uqGenerator q 1))^k) v≠0 := by
  induction k with
  | zero => simpa only [pow_zero,Module.End.one_apply] using hv
  | succ k ih =>
    intro hz
    have he := representation_E_Fpow_succ q hq hd ρ L v hE hK k
    rw [hz,map_zero] at he
    have hc : qInteger q (k+1:ℕ)*qInteger q ((L:ℤ)-k)≠0 :=
      mul_ne_zero (hqi (k+1:ℕ) (by omega) (by omega))
        (hqi ((L:ℤ)-k) (by omega) (by omega))
    have hzero : ((ρ (uqGenerator q 1))^k) v=0 :=
      (smul_eq_zero.mp he.symm).resolve_left hc
    exact ih (by omega) hzero

end AMSPhysical

#print axioms AMSPhysical.representation_E_Fpow_succ
#print axioms AMSPhysical.representation_Fpow_ne_zero
