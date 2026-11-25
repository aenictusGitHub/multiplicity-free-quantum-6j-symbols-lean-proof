import QuantumTriplePairInsertion
import QuantumMixedOscillator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def tripleLeftDegree (n : ℕ) : OccupationTripleLattice n →+ ℤ where
  toFun p := (∑ i : Fin (n+1),p.1 i)+(∑ i : Fin (n+1),p.2.1 i)
  map_zero' := by simp
  map_add' p z := by
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,Finset.sum_add_distrib]
    ring

theorem tripleLeftAnnihilation_creation_commutator (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) :
    tripleLeftAnnihilation q n*tripleLeftCreation q n-
      q^(-2:ℤ) • (tripleLeftCreation q n*tripleLeftAnnihilation q n)=
      weightedTranslation 0 (fun p : OccupationTripleLattice n =>
        q^(-tripleLeftDegree n p-(n:ℤ))*qInteger q (tripleLeftDegree n p+(n:ℤ)+1)) := by
  apply Finsupp.lhom_ext
  intro p a
  have h:=congrArg (triplePairInsert n p.2.2)
    (DFunLike.congr_fun (pairLatticeAnnihilation_creation_commutator q hq hD n) (Finsupp.single (p.1,p.2.1) a))
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul,
    triplePairInsert_annihilation,triplePairInsert_creation,triplePairInsert_single,
    weightedTranslation_single,add_zero] at h ⊢
  convert h using 1
  congr 2
  unfold tripleLeftDegree
  simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  congr 2
  ring

end AMSPhysical
#print axioms AMSPhysical.tripleLeftAnnihilation_creation_commutator
