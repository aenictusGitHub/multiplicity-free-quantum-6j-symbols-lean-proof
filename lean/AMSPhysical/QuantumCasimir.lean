import QuantumTensorRepresentation
import FiniteQuantumClebsch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def uqCasimir (q : K) : UqSL2 q :=
  (q-q⁻¹)^2 • (uqGenerator q 1*uqGenerator q 0)+q • uqGenerator q 2+q⁻¹ • uqGenerator q 3

theorem uq_F_Kinv (q : K) : uqGenerator q 1*uqGenerator q 3=
    q^(-2:ℤ) • (uqGenerator q 3*uqGenerator q 1) := by
  calc
    uqGenerator q 1*uqGenerator q 3=
      (uqGenerator q 3*uqGenerator q 2)*uqGenerator q 1*uqGenerator q 3 := by rw [uq_inverse',one_mul]
    _=uqGenerator q 3*(uqGenerator q 2*uqGenerator q 1)*uqGenerator q 3 := by noncomm_ring
    _=uqGenerator q 3*(q^(-2:ℤ) • (uqGenerator q 1*uqGenerator q 2))*uqGenerator q 3 := by rw [uq_weightF]
    _=q^(-2:ℤ) • ((uqGenerator q 3*uqGenerator q 1)*(uqGenerator q 2*uqGenerator q 3)) := by
      simp only [smul_mul_assoc,mul_smul_comm,mul_assoc]
    _=_ := by rw [uq_inverse,mul_one]

theorem uq_Kinv_F (q : K) (hq : q≠0) : uqGenerator q 3*uqGenerator q 1=
    q^2 • (uqGenerator q 1*uqGenerator q 3) := by
  have h := congrArg (fun x : UqSL2 q => q^2 • x) (uq_F_Kinv q)
  change q^2 • (uqGenerator q 1*uqGenerator q 3)=
    q^2 • (q^(-2:ℤ) • (uqGenerator q 3*uqGenerator q 1)) at h
  have hp : q^2*q^(-2:ℤ)=1 := by
    rw [← zpow_natCast q 2,← zpow_add₀ hq]
    norm_num
  rw [smul_smul,hp,one_smul] at h
  exact h.symm

theorem uqCasimir_commutes_E (q : K) (hq : q≠0) :
    uqCasimir q*uqGenerator q 0=uqGenerator q 0*uqCasimir q := by
  let D := q-q⁻¹
  have hD : D^2*D⁻¹=D := by dsimp [D]; field_simp
  have hc : uqGenerator q 1*uqGenerator q 0-uqGenerator q 0*uqGenerator q 1=
      -(D⁻¹ • (uqGenerator q 2-uqGenerator q 3)) := by
    dsimp [D]
    rw [← uq_commutator]
    abel
  have hscaled : D^2 • ((uqGenerator q 1*uqGenerator q 0-uqGenerator q 0*uqGenerator q 1)*uqGenerator q 0)=
      -(D • ((uqGenerator q 2-uqGenerator q 3)*uqGenerator q 0)) := by
    rw [hc]
    have hn : (-(D⁻¹ • (uqGenerator q 2-uqGenerator q 3)))*uqGenerator q 0=
        -((D⁻¹ • (uqGenerator q 2-uqGenerator q 3))*uqGenerator q 0) :=
      neg_mul (D⁻¹ • (uqGenerator q 2-uqGenerator q 3)) (uqGenerator q 0)
    rw [hn,smul_neg,smul_mul_assoc,smul_smul,hD]
  apply sub_eq_zero.mp
  calc
    uqCasimir q*uqGenerator q 0-uqGenerator q 0*uqCasimir q=
      D^2 • ((uqGenerator q 1*uqGenerator q 0-uqGenerator q 0*uqGenerator q 1)*uqGenerator q 0)+
      q • (uqGenerator q 2*uqGenerator q 0-uqGenerator q 0*uqGenerator q 2)+
      q⁻¹ • (uqGenerator q 3*uqGenerator q 0-uqGenerator q 0*uqGenerator q 3) := by
      simp only [uqCasimir,D,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub,sub_mul,mul_assoc]
      module
    _=(-D*q^2+q*q^2-q) • (uqGenerator q 0*uqGenerator q 2)+
        (D+q⁻¹-q⁻¹*q^2) • (uqGenerator q 3*uqGenerator q 0) := by
      rw [hscaled,sub_mul,uq_weightE,uq_E_Kinv]
      simp only [smul_sub,smul_smul]
      module
    _=0 := by
      have h₁ : -D*q^2+q*q^2-q=0 := by dsimp [D]; field_simp; ring
      have h₂ : D+q⁻¹-q⁻¹*q^2=0 := by dsimp [D]; field_simp; ring
      rw [h₁,h₂,zero_smul,zero_smul,add_zero]

theorem uqCasimir_commutes_F (q : K) (hq : q≠0) :
    uqCasimir q*uqGenerator q 1=uqGenerator q 1*uqCasimir q := by
  let D := q-q⁻¹
  have hD : D^2*D⁻¹=D := by dsimp [D]; field_simp
  have hscaled : D^2 • (uqGenerator q 1*(uqGenerator q 0*uqGenerator q 1-uqGenerator q 1*uqGenerator q 0))=
      D • (uqGenerator q 1*(uqGenerator q 2-uqGenerator q 3)) := by
    rw [uq_commutator]
    change D^2 • (uqGenerator q 1*(D⁻¹ • (uqGenerator q 2-uqGenerator q 3)))=_
    rw [mul_smul_comm,smul_smul,hD]
  apply sub_eq_zero.mp
  calc
    uqCasimir q*uqGenerator q 1-uqGenerator q 1*uqCasimir q=
      D^2 • (uqGenerator q 1*(uqGenerator q 0*uqGenerator q 1-uqGenerator q 1*uqGenerator q 0))+
      q • (uqGenerator q 2*uqGenerator q 1-uqGenerator q 1*uqGenerator q 2)+
      q⁻¹ • (uqGenerator q 3*uqGenerator q 1-uqGenerator q 1*uqGenerator q 3) := by
      simp only [uqCasimir,D,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub,mul_sub,mul_assoc]
      module
    _=(D+q*q^(-2:ℤ)-q) • (uqGenerator q 1*uqGenerator q 2)+
        (-D+q⁻¹*q^2-q⁻¹) • (uqGenerator q 1*uqGenerator q 3) := by
      rw [hscaled,mul_sub,uq_weightF,uq_Kinv_F q hq]
      simp only [smul_sub,smul_smul]
      module
    _=0 := by
      have h₁ : D+q*q^(-2:ℤ)-q=0 := by
        dsimp [D]
        simp only [zpow_neg,zpow_ofNat]
        field_simp; ring
      have h₂ : -D+q⁻¹*q^2-q⁻¹=0 := by dsimp [D]; field_simp; ring
      rw [h₁,h₂,zero_smul,zero_smul,add_zero]

theorem uqCasimir_commutes_K (q : K) (hq : q≠0) :
    uqCasimir q*uqGenerator q 2=uqGenerator q 2*uqCasimir q := by
  have hp : q^(-2:ℤ)*q^2=1 := by
    rw [← zpow_natCast q 2,← zpow_add₀ hq]
    norm_num
  have hFE : uqGenerator q 2*(uqGenerator q 1*uqGenerator q 0)=
      (uqGenerator q 1*uqGenerator q 0)*uqGenerator q 2 := by
    rw [← mul_assoc,uq_weightF,smul_mul_assoc,mul_assoc,uq_weightE,mul_smul_comm,smul_smul,hp,one_smul]
    exact (mul_assoc _ _ _).symm
  simp only [uqCasimir,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,uq_inverse,uq_inverse',hFE]

theorem uqCasimir_commutes_Kinv (q : K) (hq : q≠0) :
    uqCasimir q*uqGenerator q 3=uqGenerator q 3*uqCasimir q := by
  let u : (UqSL2 q)ˣ := ⟨uqGenerator q 2,uqGenerator q 3,uq_inverse q,uq_inverse' q⟩
  have h : Commute (uqCasimir q) (u:UqSL2 q) := uqCasimir_commutes_K q hq
  exact h.units_inv_right.eq

/-- Centrality in the independently presented quantum enveloping algebra. -/
theorem uqCasimir_central (q : K) (hq : q≠0) (x : UqSL2 q) :
    Commute (uqCasimir q) x := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (QuantumSL2Relation q) x
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    simp only [AlgHom.commutes]
    exact (Algebra.commutes r (uqCasimir q)).symm
  | grade1 i =>
    change Commute (uqCasimir q) (uqGenerator q i)
    fin_cases i
    · exact uqCasimir_commutes_E q hq
    · exact uqCasimir_commutes_F q hq
    · exact uqCasimir_commutes_K q hq
    · exact uqCasimir_commutes_Kinv q hq
  | mul a b ha hb => simp only [map_mul]; exact ha.mul_right hb
  | add a b ha hb => simp only [map_add]; exact ha.add_right hb

end AMSPhysical

#print axioms AMSPhysical.uqCasimir_commutes_E
