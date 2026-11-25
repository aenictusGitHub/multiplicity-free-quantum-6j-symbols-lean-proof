import QuantumTypeAPivotalWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem linearEnd_pow_eigen (f : Module.End K V) (a : K) (v : V) (h : f v=a • v) (r : ℕ) :
    (f^r) v=a^r • v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ,Module.End.mul_apply,h,map_smul,ih,smul_smul,pow_succ]
    rw [mul_comm a (a^r)]

theorem linearEnd_ofFn_prod_eigen (r : ℕ) (f : Fin r → Module.End K V) (a : Fin r → K)
    (v : V) (h : ∀ i,f i v=a i • v) : (List.ofFn f).prod v=(∏ i,a i) • v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ,List.prod_cons,Module.End.mul_apply,Fin.prod_univ_succ]
    rw [ih (fun i => f i.succ) (fun i => a i.succ) (fun i => h i.succ),map_smul,h,smul_smul]
    rw [mul_comm (∏ i : Fin r,a i.succ) (a 0)]

/-- The inverse pivotal element as the ordered product of the simple inverse
Cartan generators, with the standard type-A exponents. -/
def typeAInversePivot (q : K) (n : ℕ) : UqTypeA q n :=
  (List.ofFn (fun i : Fin n => (typeAAlgebraGenerator q n i 3)^(typeAPivotalExponent n i))).prod

theorem typeAInversePivot_basis (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) :
    typeAFiniteQuantumRepresentation q hq hD n L (typeAInversePivot q n)
      (quantumOccupationBasis (K:=ℝ) L x)=
      q^(latticePairing (typeAInversePivotalWeight n) x.val) • quantumOccupationBasis (K:=ℝ) L x := by
  unfold typeAInversePivot
  rw [map_list_prod,List.map_ofFn]
  change (List.ofFn (fun i : Fin n => typeAFiniteQuantumRepresentation q hq hD n L
    ((typeAAlgebraGenerator q n i 3)^(typeAPivotalExponent n i)))).prod
    (quantumOccupationBasis (K:=ℝ) L x)=_
  simp only [map_pow]
  change (List.ofFn (fun i : Fin n => (typeAFiniteGenerator q hq hD n L i 3)^
    (typeAPivotalExponent n i))).prod (quantumOccupationBasis (K:=ℝ) L x)=_
  rw [linearEnd_ofFn_prod_eigen n _
    (fun i => (q^(-simpleOccupationWeight n x.val i))^(typeAPivotalExponent n i)) _
    (fun i => linearEnd_pow_eigen _ _ _ (typeAFiniteGenerator_Ki_basis q hq hD n L i x) _)]
  congr 1
  calc
    _ = ∏ i : Fin n,q^((typeAPivotalExponent n i : ℤ)*(x.val i.succ-x.val i.castSucc)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← zpow_natCast (q^(-simpleOccupationWeight n x.val i)),← zpow_mul]
      congr 1
      unfold simpleOccupationWeight
      ring
    _ = q^(∑ i : Fin n,(typeAPivotalExponent n i : ℤ)*(x.val i.succ-x.val i.castSucc)) :=
      (zpow_finset_sum q hq Finset.univ _).symm
    _ = _ := by rw [typeAPivotalWeight_pairing]

theorem typeAInversePivot_representation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n L : ℕ) :
    typeAFiniteQuantumRepresentation q hq hD n L (typeAInversePivot q n)=
      finiteOccupationCartan q L (typeAInversePivotalWeight n) := by
  apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
  intro x
  rw [typeAInversePivot_basis,finiteOccupationCartan_basis]

/-- The actual presented-algebra pivotal trace of the constructed symmetric
irrep is the closed quantum Weyl dimension, in every rank and degree. -/
theorem typeASymmetric_pivotal_dimension (q : ℝ) (hq : 0<q) (hD : q-q⁻¹≠0) (n L : ℕ) :
    LinearMap.trace ℝ (quantumOccupationSpace ℝ (Fin (n+1)) L)
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) hD n L (typeAInversePivot q n))=
      qfactorial q (n+L)/(qfactorial q n*qfactorial q L) := by
  rw [typeAInversePivot_representation]
  exact inversePivotal_trace_factorial q hq n L

end AMSPhysical
#print axioms AMSPhysical.typeASymmetric_pivotal_dimension
