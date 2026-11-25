import TensorWeightedHilbert
import Mathlib.LinearAlgebra.TensorProduct.Associator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {ι κ ι' κ' V W V' W' : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype ι'] [Fintype κ'] [DecidableEq ι'] [DecidableEq κ']
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem tensorWeightedBilin_map_isometry
    (b : Basis ι ℝ V) (c : Basis κ ℝ W) (b' : Basis ι' ℝ V') (c' : Basis κ' ℝ W')
    (w : ι → ℝ) (z : κ → ℝ) (w' : ι' → ℝ) (z' : κ' → ℝ)
    (A : V →ₗ[ℝ] V') (D : W →ₗ[ℝ] W')
    (hA : ∀ p v,finiteWeightedPair w' b'.equivFun.toLinearMap (A p) (A v)=
      finiteWeightedPair w b.equivFun.toLinearMap p v)
    (hD : ∀ p v,finiteWeightedPair z' c'.equivFun.toLinearMap (D p) (D v)=
      finiteWeightedPair z c.equivFun.toLinearMap p v) (p v : V ⊗[ℝ] W) :
    tensorWeightedBilin b' c' w' z' (TensorProduct.map A D p) (TensorProduct.map A D v)=
      tensorWeightedBilin b c w z p v := by
  have he : ((tensorWeightedBilin b' c' w' z').comp (TensorProduct.map A D)).compl₂
      (TensorProduct.map A D)=tensorWeightedBilin b c w z := by
    apply (b.tensorProduct c).ext
    intro ij
    apply (b.tensorProduct c).ext
    intro kl
    change tensorWeightedBilin b' c' w' z' (TensorProduct.map A D ((b.tensorProduct c) ij))
      (TensorProduct.map A D ((b.tensorProduct c) kl))=tensorWeightedBilin b c w z _ _
    rw [Basis.tensorProduct_apply',Basis.tensorProduct_apply',TensorProduct.map_tmul,
      TensorProduct.map_tmul,tensorWeightedBilin_tmul,tensorWeightedBilin_tmul]
    rw [hA,hD]
  exact DFunLike.congr_fun (DFunLike.congr_fun he p) v

variable {η U : Type*} [Fintype η] [DecidableEq η] [AddCommGroup U] [Module ℝ U]

theorem tensorWeightedBilin_assoc_isometry (b : Basis ι ℝ V) (c : Basis κ ℝ W) (d : Basis η ℝ U)
    (w : ι → ℝ) (z : κ → ℝ) (u : η → ℝ) (p v : (V ⊗[ℝ] W) ⊗[ℝ] U) :
    tensorWeightedBilin b (c.tensorProduct d) w (fun jk => z jk.1*u jk.2)
      ((TensorProduct.assoc ℝ V W U) p) ((TensorProduct.assoc ℝ V W U) v)=
    tensorWeightedBilin (b.tensorProduct c) d (fun ij => w ij.1*z ij.2) u p v := by
  let BL := tensorWeightedBilin (b.tensorProduct c) d (fun ij => w ij.1*z ij.2) u
  let BR := tensorWeightedBilin b (c.tensorProduct d) w (fun jk => z jk.1*u jk.2)
  let A := (TensorProduct.assoc ℝ V W U).toLinearMap
  have he : (BR.comp A).compl₂ A=BL := by
    apply ((b.tensorProduct c).tensorProduct d).ext
    intro ijk
    apply ((b.tensorProduct c).tensorProduct d).ext
    intro i'j'k'
    change BR (A (((b.tensorProduct c).tensorProduct d) ijk))
      (A (((b.tensorProduct c).tensorProduct d) i'j'k'))=BL _ _
    dsimp only [A,BL,BR]
    rw [Basis.tensorProduct_apply',Basis.tensorProduct_apply',Basis.tensorProduct_apply',
      Basis.tensorProduct_apply',LinearEquiv.coe_coe,TensorProduct.assoc_tmul,TensorProduct.assoc_tmul,
      tensorWeightedBilin_tmul,tensorWeightedBilin_tmul]
    change finiteWeightedPair w b.equivFun.toLinearMap _ _*
      tensorWeightedBilin c d z u _ _=
      tensorWeightedBilin b c w z _ _*finiteWeightedPair u d.equivFun.toLinearMap _ _
    rw [tensorWeightedBilin_tmul,tensorWeightedBilin_tmul]
    ring
  exact DFunLike.congr_fun (DFunLike.congr_fun he p) v

end AMSPhysical

#print axioms AMSPhysical.tensorWeightedBilin_assoc_isometry
