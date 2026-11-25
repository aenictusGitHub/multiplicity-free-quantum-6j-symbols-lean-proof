import QuantumAlgebra
import Mathlib.RingTheory.TensorProduct.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

def uqGenerator (q : K) (i : Fin 4) : UqSL2 q :=
  RingQuot.mkAlgHom K (QuantumSL2Relation q) (FreeAlgebra.ι K i)

theorem uq_inverse (q : K) : uqGenerator q 2*uqGenerator q 3=1 := by
  simpa only [uqGenerator,map_mul,map_one] using
    RingQuot.mkAlgHom_rel K (QuantumSL2Relation.inverse (q:=q))

theorem uq_inverse' (q : K) : uqGenerator q 3*uqGenerator q 2=1 := by
  simpa only [uqGenerator,map_mul,map_one] using
    RingQuot.mkAlgHom_rel K (QuantumSL2Relation.inverse' (q:=q))

theorem uq_weightE (q : K) : uqGenerator q 2*uqGenerator q 0=
    q^2 • (uqGenerator q 0*uqGenerator q 2) := by
  simpa only [uqGenerator,map_mul,map_smul] using
    RingQuot.mkAlgHom_rel K (QuantumSL2Relation.weightE (q:=q))

theorem uq_weightF (q : K) : uqGenerator q 2*uqGenerator q 1=
    q^(-2:ℤ) • (uqGenerator q 1*uqGenerator q 2) := by
  simpa only [uqGenerator,map_mul,map_smul] using
    RingQuot.mkAlgHom_rel K (QuantumSL2Relation.weightF (q:=q))

theorem uq_commutator (q : K) : uqGenerator q 0*uqGenerator q 1-uqGenerator q 1*uqGenerator q 0=
    (q-q⁻¹)⁻¹ • (uqGenerator q 2-uqGenerator q 3) := by
  simpa only [uqGenerator,map_mul,map_sub,map_smul] using
    RingQuot.mkAlgHom_rel K (QuantumSL2Relation.commutator (q:=q))

theorem uq_E_Kinv (q : K) : uqGenerator q 0*uqGenerator q 3=
    q^2 • (uqGenerator q 3*uqGenerator q 0) := by
  calc
    uqGenerator q 0*uqGenerator q 3=
      (uqGenerator q 3*uqGenerator q 2)*uqGenerator q 0*uqGenerator q 3 := by rw [uq_inverse',one_mul]
    _=uqGenerator q 3*(uqGenerator q 2*uqGenerator q 0)*uqGenerator q 3 := by noncomm_ring
    _=uqGenerator q 3*(q^2 • (uqGenerator q 0*uqGenerator q 2))*uqGenerator q 3 := by rw [uq_weightE]
    _=q^2 • ((uqGenerator q 3*uqGenerator q 0)*(uqGenerator q 2*uqGenerator q 3)) := by
      simp only [smul_mul_assoc,mul_smul_comm,mul_assoc]
    _=_ := by rw [uq_inverse,mul_one]

def coproductE (q : K) : UqSL2 q ⊗[K] UqSL2 q :=
  uqGenerator q 0 ⊗ₜ[K] uqGenerator q 2+(1:UqSL2 q) ⊗ₜ[K] uqGenerator q 0

def coproductF (q : K) : UqSL2 q ⊗[K] UqSL2 q :=
  uqGenerator q 1 ⊗ₜ[K] (1:UqSL2 q)+uqGenerator q 3 ⊗ₜ[K] uqGenerator q 1

def coproductK (q : K) : UqSL2 q ⊗[K] UqSL2 q :=
  uqGenerator q 2 ⊗ₜ[K] uqGenerator q 2

def coproductKinv (q : K) : UqSL2 q ⊗[K] UqSL2 q :=
  uqGenerator q 3 ⊗ₜ[K] uqGenerator q 3

theorem coproduct_inverse (q : K) : coproductK q*coproductKinv q=1 := by
  simp only [coproductK,coproductKinv,Algebra.TensorProduct.tmul_mul_tmul,uq_inverse,
    ← Algebra.TensorProduct.one_def]

theorem coproduct_inverse' (q : K) : coproductKinv q*coproductK q=1 := by
  simp only [coproductK,coproductKinv,Algebra.TensorProduct.tmul_mul_tmul,uq_inverse',
    ← Algebra.TensorProduct.one_def]

theorem coproduct_weightE (q : K) : coproductK q*coproductE q=q^2 • (coproductE q*coproductK q) := by
  simp only [coproductK,coproductE,mul_add,add_mul,Algebra.TensorProduct.tmul_mul_tmul,
    mul_one,one_mul,uq_weightE,TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_add]

theorem coproduct_weightF (q : K) : coproductK q*coproductF q=
    q^(-2:ℤ) • (coproductF q*coproductK q) := by
  simp only [coproductK,coproductF,mul_add,add_mul,Algebra.TensorProduct.tmul_mul_tmul,
    mul_one,one_mul,uq_inverse,uq_inverse',uq_weightF,TensorProduct.smul_tmul',
    TensorProduct.tmul_smul,smul_add]

theorem coproduct_cross_commutes (q : K) (hq : q≠0) :
    (uqGenerator q 0 ⊗ₜ[K] uqGenerator q 2)*(uqGenerator q 3 ⊗ₜ[K] uqGenerator q 1)=
      (uqGenerator q 3 ⊗ₜ[K] uqGenerator q 1)*(uqGenerator q 0 ⊗ₜ[K] uqGenerator q 2) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul,uq_E_Kinv,uq_weightF,
    ← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul]
  have he : q^2*q^(-2:ℤ)=1 := by
    rw [← zpow_natCast q 2,← zpow_add₀ hq]
    norm_num
  rw [mul_comm (q^(-2:ℤ)) (q^2),he,one_smul]

theorem coproduct_commutator (q : K) (hq : q≠0) :
    coproductE q*coproductF q-coproductF q*coproductE q=
      (q-q⁻¹)⁻¹ • (coproductK q-coproductKinv q) := by
  have hc := coproduct_cross_commutes q hq
  have hc' : ((1:UqSL2 q) ⊗ₜ[K] uqGenerator q 0)*(uqGenerator q 1 ⊗ₜ[K] (1:UqSL2 q))=
      (uqGenerator q 1 ⊗ₜ[K] (1:UqSL2 q))*((1:UqSL2 q) ⊗ₜ[K] uqGenerator q 0) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]
  calc
    coproductE q*coproductF q-coproductF q*coproductE q=
      ((uqGenerator q 0 ⊗ₜ[K] uqGenerator q 2)*(uqGenerator q 1 ⊗ₜ[K] (1:UqSL2 q))-
        (uqGenerator q 1 ⊗ₜ[K] (1:UqSL2 q))*(uqGenerator q 0 ⊗ₜ[K] uqGenerator q 2))+
      (((1:UqSL2 q) ⊗ₜ[K] uqGenerator q 0)*(uqGenerator q 3 ⊗ₜ[K] uqGenerator q 1)-
        (uqGenerator q 3 ⊗ₜ[K] uqGenerator q 1)*((1:UqSL2 q) ⊗ₜ[K] uqGenerator q 0)) := by
      unfold coproductE coproductF
      simp only [mul_add,add_mul]
      rw [hc,hc']
      abel
    _=(uqGenerator q 0*uqGenerator q 1-uqGenerator q 1*uqGenerator q 0) ⊗ₜ[K] uqGenerator q 2+
      uqGenerator q 3 ⊗ₜ[K] (uqGenerator q 0*uqGenerator q 1-uqGenerator q 1*uqGenerator q 0) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul,TensorProduct.sub_tmul,
        TensorProduct.tmul_sub]
    _=_ := by
      rw [uq_commutator]
      simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,
        TensorProduct.sub_tmul,TensorProduct.tmul_sub,smul_add,smul_sub,coproductK,coproductKinv]
      abel

def coproductFree (q : K) : FreeAlgebra K (Fin 4) →ₐ[K] (UqSL2 q ⊗[K] UqSL2 q) :=
  FreeAlgebra.lift K ![coproductE q,coproductF q,coproductK q,coproductKinv q]

theorem coproductFree_respects (q : K) (hq : q≠0)
    {x y : FreeAlgebra K (Fin 4)} (h : QuantumSL2Relation q x y) :
    coproductFree q x=coproductFree q y := by
  cases h
  · simpa [coproductFree] using coproduct_inverse q
  · simpa [coproductFree] using coproduct_inverse' q
  · simpa [coproductFree] using coproduct_weightE q
  · simpa [coproductFree] using coproduct_weightF q
  · simpa [coproductFree] using coproduct_commutator q hq

/-- The standard coproduct on the independently presented quantum algebra. -/
def quantumCoproduct (q : K) (hq : q≠0) : UqSL2 q →ₐ[K] (UqSL2 q ⊗[K] UqSL2 q) :=
  RingQuot.liftAlgHom K ⟨coproductFree q,by intro x y h; exact coproductFree_respects q hq h⟩

theorem quantumCoproduct_generator (q : K) (hq : q≠0) (i : Fin 4) :
    quantumCoproduct q hq (uqGenerator q i)=
      ![coproductE q,coproductF q,coproductK q,coproductKinv q] i := by
  simp [uqGenerator,quantumCoproduct,coproductFree,RingQuot.liftAlgHom_mkAlgHom_apply]

end AMSPhysical

#print axioms AMSPhysical.coproduct_weightE
