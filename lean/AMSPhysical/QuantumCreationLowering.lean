import QuantumCreationRaising

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def pairLatticeSwap (n : ℕ) : Module.End ℝ (OccupationPairLattice n →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ Prod.swap

@[simp] theorem pairLatticeSwap_single (n : ℕ) (p : OccupationPairLattice n) (a : ℝ) :
    pairLatticeSwap n (Finsupp.single p a)=Finsupp.single p.swap a :=
  Finsupp.mapDomain_single

theorem pairLatticeSwap_involutive (n : ℕ) : Function.Involutive (pairLatticeSwap n) := by
  have he : (pairLatticeSwap n).comp (pairLatticeSwap n)=LinearMap.id := by
    apply Finsupp.lhom_ext
    intro p a
    simp
  intro f
  exact DFunLike.congr_fun he f

theorem pairLatticeSwap_injective (n : ℕ) : Function.Injective (pairLatticeSwap n) :=
  (pairLatticeSwap_involutive n).injective

def pairLatticeLowering (q : ℝ) (n : ℕ) (i : Fin n) : Module.End ℝ (OccupationPairLattice n →₀ ℝ) :=
  weightedTranslation (-latticeRoot i.castSucc i.succ,0) (fun p =>qInteger q (p.1 i.castSucc))+
  weightedTranslation (0,latticeRoot i.castSucc i.succ)
    (fun p =>q^(-simpleOccupationWeight n p.1 i)*qInteger q (p.2 i.succ))

theorem pairLatticeSwap_raising (q : ℝ) (n : ℕ) (i : Fin n)
    (f : OccupationPairLattice n →₀ ℝ) :
    pairLatticeSwap n (pairLatticeRaising q n i f)=pairLatticeLowering q n i (pairLatticeSwap n f) := by
  have he : (pairLatticeSwap n).comp (pairLatticeRaising q n i)=
      (pairLatticeLowering q n i).comp (pairLatticeSwap n) := by
    apply Finsupp.lhom_ext
    intro p a
    simp only [LinearMap.comp_apply,pairLatticeRaising,pairLatticeLowering,LinearMap.add_apply,
      weightedTranslation_single,map_add,pairLatticeSwap_single]
    simp only [Prod.swap_add,Prod.swap_prod_mk]
    rw [add_comm]
    congr 1
    congr 1
    dsimp only [Prod.swap]
    ring
  exact DFunLike.congr_fun he f

theorem pairLatticeSwap_lowering (q : ℝ) (n : ℕ) (i : Fin n)
    (f : OccupationPairLattice n →₀ ℝ) :
    pairLatticeSwap n (pairLatticeLowering q n i f)=pairLatticeRaising q n i (pairLatticeSwap n f) := by
  apply pairLatticeSwap_injective n
  rw [pairLatticeSwap_involutive,pairLatticeSwap_raising,pairLatticeSwap_involutive]

theorem mixedCreationCoefficient_swap (q : ℝ) (n : ℕ) (k : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n k p.swap=mixedCreationCoefficient q n k p := by
  unfold mixedCreationCoefficient Prod.swap
  congr 1
  ring

theorem pairLatticeSwap_creation (q : ℝ) (n : ℕ) (f : OccupationPairLattice n →₀ ℝ) :
    pairLatticeSwap n (pairLatticeCreation q n f)=pairLatticeCreation q n (pairLatticeSwap n f) := by
  have he : (pairLatticeSwap n).comp (pairLatticeCreation q n)=
      (pairLatticeCreation q n).comp (pairLatticeSwap n) := by
    apply Finsupp.lhom_ext
    intro p a
    simp only [LinearMap.comp_apply,pairLatticeCreation,LinearMap.sum_apply,
      weightedTranslation_single,map_sum,pairLatticeSwap_single]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mixedCreationCoefficient_swap]
    rfl
  exact DFunLike.congr_fun he f

/-- Lowering commutation follows from the independently verified literal
factor-exchange identities, rather than an assumed abstract star operation. -/
theorem pairLatticeCreation_commutes_lowering (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (n : ℕ) (i : Fin n) :
    pairLatticeCreation q n*pairLatticeLowering q n i=
      pairLatticeLowering q n i*pairLatticeCreation q n := by
  apply LinearMap.ext
  intro f
  apply pairLatticeSwap_injective n
  change pairLatticeSwap n (pairLatticeCreation q n (pairLatticeLowering q n i f))=
    pairLatticeSwap n (pairLatticeLowering q n i (pairLatticeCreation q n f))
  rw [pairLatticeSwap_creation,pairLatticeSwap_lowering,pairLatticeSwap_lowering,pairLatticeSwap_creation]
  exact DFunLike.congr_fun (pairLatticeCreation_commutes_raising q hq hD n i) (pairLatticeSwap n f)

end AMSPhysical
#print axioms AMSPhysical.pairLatticeCreation_commutes_lowering
