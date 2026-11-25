import QuantumTripleReverseInsertion
import QuantumMixedOscillator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def tripleRightDegree (n : ℕ) : OccupationTripleLattice n →+ ℤ where
  toFun p := (∑ i : Fin (n+1),p.2.1 i)+(∑ i : Fin (n+1),p.2.2 i)
  map_zero' := by simp
  map_add' p z := by
    simp only [Prod.snd_add,Prod.fst_add,Pi.add_apply,Finset.sum_add_distrib]
    ring

theorem tripleRightAnnihilation_creation_commutator (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) :
    tripleRightAnnihilation q n*tripleRightCreation q n-
      q^(-2:ℤ) • (tripleRightCreation q n*tripleRightAnnihilation q n)=
      weightedTranslation 0 (fun p : OccupationTripleLattice n =>
        q^(-tripleRightDegree n p-(n:ℤ))*qInteger q (tripleRightDegree n p+(n:ℤ)+1)) := by
  apply Finsupp.lhom_ext
  intro p a
  have h:=congrArg (tripleReversePairInsert n p.1)
    (DFunLike.congr_fun (pairLatticeAnnihilation_creation_commutator q hq hD n)
      (Finsupp.single (occupationLatticeReflect n p.2.1,occupationLatticeReflect n p.2.2) a))
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul,
    tripleReversePairInsert_annihilation,tripleReversePairInsert_creation,tripleReversePairInsert_single,
    occupationLatticeReflect_involution,weightedTranslation_single,add_zero,occupationLatticeReflect_sum] at h ⊢
  convert h using 1
  congr 2
  unfold tripleRightDegree
  simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  congr 2
  ring

end AMSPhysical
#print axioms AMSPhysical.tripleRightAnnihilation_creation_commutator
