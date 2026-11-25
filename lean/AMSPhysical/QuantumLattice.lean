import QuantumNumbers
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

variable {K ι : Type*} [Field K] [DecidableEq ι]

abbrev QuantumLatticeSpace (K ι : Type*) [Field K] := (ι → ℤ) →₀ K

def latticeShift (s : ι → ℤ) (w : (ι → ℤ) → K) : Module.End K (QuantumLatticeSpace K ι) :=
  Finsupp.lsum K (fun x => LinearMap.toSpanSingleton K _ (Finsupp.single (x+s) (w x)))

@[simp] theorem latticeShift_single (s : ι → ℤ) (w : (ι → ℤ) → K) (x : ι → ℤ) (a : K) :
    latticeShift s w (Finsupp.single x a)=Finsupp.single (x+s) (a*w x) := by
  unfold latticeShift
  rw [Finsupp.lsum_single]
  simp only [LinearMap.toSpanSingleton_apply,Finsupp.smul_single,smul_eq_mul]

theorem latticeShift_mul (s t : ι → ℤ) (w v : (ι → ℤ) → K) :
    latticeShift s w*latticeShift t v=latticeShift (s+t) (fun x => v x*w (x+t)) := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [Module.End.mul_apply,latticeShift_single]
  have hi : x+t+s=x+(s+t) := by funext i;simp only [Pi.add_apply];ring
  rw [hi]
  congr 1
  ring

theorem latticeShift_one : latticeShift (0 : ι → ℤ) (fun _ => (1:K))=1 := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [latticeShift_single,add_zero,mul_one,Module.End.one_apply]

def latticeRoot (i j : ι) : ι → ℤ := Pi.single i 1-Pi.single j 1

def quantumLatticeMove (q : K) (i j : ι) : Module.End K (QuantumLatticeSpace K ι) :=
  latticeShift (latticeRoot i j) (fun x => qInteger q (x j))

theorem latticeRoot_swap (i j : ι) : latticeRoot j i= -latticeRoot i j := by
  unfold latticeRoot
  abel

theorem latticeRoot_self (i : ι) : latticeRoot i i=0 := by simp [latticeRoot]

theorem latticeRoot_target (i j : ι) (hij : i≠j) : latticeRoot i j i=1 := by
  simp [latticeRoot,Pi.single_apply,hij,Ne.symm hij]

theorem latticeRoot_source (i j : ι) (hij : i≠j) : latticeRoot i j j= -1 := by
  simp [latticeRoot,Pi.single_apply,hij,Ne.symm hij]

theorem latticeRoot_other (i j k : ι) (hki : k≠i) (hkj : k≠j) : latticeRoot i j k=0 := by
  simp [latticeRoot,Pi.single_apply,hki,hkj,Ne.symm hki,Ne.symm hkj]

@[simp] theorem quantumLatticeMove_single (q : K) (i j : ι) (x : ι → ℤ) (a : K) :
    quantumLatticeMove q i j (Finsupp.single x a)=Finsupp.single (x+latticeRoot i j) (a*qInteger q (x j)) :=
  latticeShift_single _ _ _ _

section Torus
variable [Fintype ι]

def latticePairing (h x : ι → ℤ) : ℤ := ∑ i,h i*x i

theorem latticePairing_add_right (h x y : ι → ℤ) :
    latticePairing h (x+y)=latticePairing h x+latticePairing h y := by
  simp only [latticePairing,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem latticePairing_add_left (h g x : ι → ℤ) :
    latticePairing (h+g) x=latticePairing h x+latticePairing g x := by
  simp only [latticePairing,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem latticePairing_root_right (h : ι → ℤ) (i j : ι) :
    latticePairing h (latticeRoot i j)=h i-h j := by
  simp [latticePairing,latticeRoot,Pi.single_apply,mul_sub,Finset.sum_sub_distrib,mul_ite]

theorem latticePairing_root_left (x : ι → ℤ) (i j : ι) :
    latticePairing (latticeRoot i j) x=x i-x j := by
  simp [latticePairing,latticeRoot,Pi.single_apply,sub_mul,Finset.sum_sub_distrib,ite_mul]

def quantumLatticeCartan (q : K) (h : ι → ℤ) : Module.End K (QuantumLatticeSpace K ι) :=
  latticeShift 0 (fun x => q^(latticePairing h x))

@[simp] theorem quantumLatticeCartan_single (q : K) (h x : ι → ℤ) (a : K) :
    quantumLatticeCartan q h (Finsupp.single x a)=Finsupp.single x (a*q^(latticePairing h x)) := by
  simp only [quantumLatticeCartan,latticeShift_single,add_zero]

theorem quantumLatticeCartan_zero (q : K) : quantumLatticeCartan q (0 : ι → ℤ)=1 := by
  simpa only [quantumLatticeCartan,latticePairing,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zpow_zero]
    using (latticeShift_one (K:=K) (ι:=ι))

theorem quantumLatticeCartan_mul (q : K) (hq : q≠0) (h g : ι → ℤ) :
    quantumLatticeCartan q h*quantumLatticeCartan q g=quantumLatticeCartan q (h+g) := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [Module.End.mul_apply,quantumLatticeCartan_single,latticePairing_add_left,zpow_add₀ hq]
  congr 1
  ring

theorem quantumLatticeCartan_inverse (q : K) (hq : q≠0) (h : ι → ℤ) :
    quantumLatticeCartan q h*quantumLatticeCartan q (-h)=1 := by
  rw [quantumLatticeCartan_mul q hq,add_neg_cancel,quantumLatticeCartan_zero]

theorem quantumLatticeCartan_shift (q : K) (hq : q≠0) (h s : ι → ℤ) (w : (ι → ℤ) → K) :
    quantumLatticeCartan q h*latticeShift s w=
      q^(latticePairing h s) • (latticeShift s w*quantumLatticeCartan q h) := by
  apply Finsupp.lhom_ext
  intro x a
  simp only [Module.End.mul_apply,quantumLatticeCartan_single,latticeShift_single,LinearMap.smul_apply,
    Finsupp.smul_single,smul_eq_mul,latticePairing_add_right,zpow_add₀ hq]
  congr 1
  ring

theorem quantumLatticeCartan_move (q : K) (hq : q≠0) (h : ι → ℤ) (i j : ι) :
    quantumLatticeCartan q h*quantumLatticeMove q i j=
      q^(h i-h j) • (quantumLatticeMove q i j*quantumLatticeCartan q h) := by
  simpa only [quantumLatticeMove,latticePairing_root_right] using
    quantumLatticeCartan_shift q hq h (latticeRoot i j) (fun x => qInteger q (x j))

end Torus
end AMSPhysical

#print axioms AMSPhysical.quantumLatticeCartan_move
