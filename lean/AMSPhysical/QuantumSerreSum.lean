import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

def serrePolynomial (q : K) (X Y : A) : A := X*X*Y-(q+q⁻¹) • (X*Y*X)+Y*X*X

def serreCross (q : K) (X Z Y : A) : A :=
  X*Z*Y+Z*X*Y-(q+q⁻¹) • (X*Y*Z+Z*Y*X)+Y*X*Z+Y*Z*X

theorem serrePolynomial_add (q : K) (X Z Y W : A) :
    serrePolynomial q (X+Z) (Y+W)=
      serrePolynomial q X Y+serrePolynomial q X W+serrePolynomial q Z Y+serrePolynomial q Z W+
        serreCross q X Z Y+serreCross q X Z W := by
  unfold serrePolynomial serreCross
  simp only [add_mul,mul_add,smul_add,mul_assoc]
  abel

theorem serrePolynomial_qcommute (q r : K) (X Y : A) (hXY : X*Y=r • (Y*X)) :
    serrePolynomial q X Y=(r^2-(q+q⁻¹)*r+1) • (Y*X*X) := by
  have h₁ : X*X*Y=r^2 • (Y*X*X) := by
    calc
      _ = X*(X*Y) := by noncomm_ring
      _ = r • (X*Y*X) := by
        conv_lhs => rw [hXY]
        rw [mul_smul_comm]
        congr 1
        noncomm_ring
      _ = r^2 • (Y*X*X) := by rw [hXY,smul_mul_assoc,smul_smul,pow_two]
  have h₂ : X*Y*X=r • (Y*X*X) := by rw [hXY,smul_mul_assoc]
  rw [serrePolynomial,h₁,h₂,smul_smul]
  module

theorem serre_q_scalar (q : K) (hq : q≠0) : q^2-(q+q⁻¹)*q+1=0 := by field_simp [hq];ring

theorem serre_qinv_scalar (q : K) (hq : q≠0) : (q⁻¹)^2-(q+q⁻¹)*q⁻¹+1=0 := by field_simp [hq];ring

theorem serreCross_right_commute (q : K) (hq : q≠0) (X Z Y : A)
    (hXZ : X*Z=q^2 • (Z*X)) (hZY : Z*Y=q • (Y*Z)) : serreCross q X Z Y=0 := by
  have hZX : Z*X=(q⁻¹)^2 • (X*Z) := by
    calc
      _ = (q^2)⁻¹ • (q^2 • (Z*X)) := (inv_smul_smul₀ (pow_ne_zero 2 hq) _).symm
      _ = (q⁻¹)^2 • (X*Z) := by rw [← hXZ,← inv_pow]
  have hs : q*(q⁻¹)^2=q⁻¹ := by field_simp [hq]
  have h₁ : X*Z*Y=q • (X*Y*Z) := by rw [mul_assoc,hZY,mul_smul_comm];simp only [mul_assoc]
  have h₂ : Z*X*Y=q⁻¹ • (X*Y*Z) := by
    rw [hZX,smul_mul_assoc,h₁,smul_smul,mul_comm ((q⁻¹)^2) q,hs]
  have h₃ : Z*Y*X=q⁻¹ • (Y*X*Z) := by
    rw [hZY,smul_mul_assoc,mul_assoc Y,hZX,mul_smul_comm,smul_smul,hs]
    simp only [mul_assoc]
  have h₄ : Y*Z*X=(q⁻¹)^2 • (Y*X*Z) := by rw [mul_assoc,hZX,mul_smul_comm];simp only [mul_assoc]
  rw [serreCross,h₁,h₂,h₃,h₄]
  have hz : (q⁻¹)^2+1-(q+q⁻¹)*q⁻¹=0 := by linear_combination serre_qinv_scalar q hq
  calc
    _ = ((q⁻¹)^2+1-(q+q⁻¹)*q⁻¹) • (Y*X*Z) := by module
    _ = 0 := by rw [hz,zero_smul]

theorem serreCross_left_commute (q : K) (hq : q≠0) (X Z Y : A)
    (hXZ : X*Z=q^2 • (Z*X)) (hXY : X*Y=q⁻¹ • (Y*X)) : serreCross q X Z Y=0 := by
  have hZX : Z*X=(q⁻¹)^2 • (X*Z) := by
    calc
      _ = (q^2)⁻¹ • (q^2 • (Z*X)) := (inv_smul_smul₀ (pow_ne_zero 2 hq) _).symm
      _ = (q⁻¹)^2 • (X*Z) := by rw [← hXZ,← inv_pow]
  have hYX : Y*X=q • (X*Y) := by
    calc
      _ = q • (q⁻¹ • (Y*X)) := (smul_inv_smul₀ hq _).symm
      _ = _ := by rw [← hXY]
  have hs : q*(q⁻¹)^2=q⁻¹ := by field_simp [hq]
  have h₁ : Z*X*Y=(q⁻¹)^2 • (X*Z*Y) := by rw [hZX,smul_mul_assoc]
  have h₂ : X*Y*Z=q⁻¹ • (Y*X*Z) := by rw [hXY,smul_mul_assoc]
  have h₃ : Z*Y*X=q⁻¹ • (X*Z*Y) := by
    rw [mul_assoc Z,hYX,mul_smul_comm,← mul_assoc,hZX,smul_mul_assoc,smul_smul,hs]
  have h₄ : Y*Z*X=(q⁻¹)^2 • (Y*X*Z) := by rw [mul_assoc,hZX,mul_smul_comm];simp only [mul_assoc]
  rw [serreCross,h₁,h₂,h₃,h₄]
  have hz : (q⁻¹)^2+1-(q+q⁻¹)*q⁻¹=0 := by linear_combination serre_qinv_scalar q hq
  calc
    _ = ((q⁻¹)^2+1-(q+q⁻¹)*q⁻¹) • (X*Z*Y)+
      ((q⁻¹)^2+1-(q+q⁻¹)*q⁻¹) • (Y*X*Z) := by module
    _ = 0 := by simp only [hz,zero_smul,zero_add]

/-- The algebraic Serre mechanism for the standard coproduct, proved without
assuming a quantum-group tensor-product representation. -/
theorem serrePolynomial_coproduct_sum (q : K) (hq : q≠0) (X Z Y W : A)
    (hXZ : X*Z=q^2 • (Z*X)) (hXW : X*W=q⁻¹ • (W*X)) (hZY : Z*Y=q • (Y*Z))
    (hXY : serrePolynomial q X Y=0) (hZW : serrePolynomial q Z W=0) :
    serrePolynomial q (X+Z) (Y+W)=0 := by
  rw [serrePolynomial_add,hXY,hZW,serreCross_right_commute q hq X Z Y hXZ hZY,
    serreCross_left_commute q hq X Z W hXZ hXW,
    serrePolynomial_qcommute q q⁻¹ X W hXW,serre_qinv_scalar q hq,zero_smul,
    serrePolynomial_qcommute q q Z Y hZY,serre_q_scalar q hq,zero_smul]
  simp only [add_zero,zero_add]

end AMSPhysical

#print axioms AMSPhysical.serrePolynomial_coproduct_sum
