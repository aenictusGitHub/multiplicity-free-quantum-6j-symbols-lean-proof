import QuantumTypeARelations
import QuantumCoproduct

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K : Type*} [Field K]

def rankTwoToSL2Free (q : K) : FreeAlgebra K (Fin 1×Fin 4) →ₐ[K] UqSL2 q :=
  FreeAlgebra.lift K (fun it =>uqGenerator q it.2)

theorem rankTwoToSL2Free_respects (q : K)
    {x y : FreeAlgebra K (Fin 1×Fin 4)} (h : QuantumTypeARelation q 1 x y) :
    rankTwoToSL2Free q x=rankTwoToSL2Free q y := by
  cases h with
  | inverse i => simpa [rankTwoToSL2Free,typeAFreeGenerator] using uq_inverse q
  | inverse' i => simpa [rankTwoToSL2Free,typeAFreeGenerator] using uq_inverse' q
  | torus i j => simp [rankTwoToSL2Free,typeAFreeGenerator]
  | weightE i j =>
    have hij : i=j := Subsingleton.elim _ _
    simpa [rankTwoToSL2Free,typeAFreeGenerator,typeACartan,hij,zpow_ofNat] using uq_weightE q
  | weightF i j =>
    have hij : i=j := Subsingleton.elim _ _
    simpa [rankTwoToSL2Free,typeAFreeGenerator,typeACartan,hij,zpow_ofNat] using uq_weightF q
  | commutator i => simpa [rankTwoToSL2Free,typeAFreeGenerator] using uq_commutator q
  | differentEF i j hij => exact False.elim (hij (Subsingleton.elim _ _))
  | distantE i j hd => have hi:=i.isLt;have hj:=j.isLt;omega
  | distantF i j hd => have hi:=i.isLt;have hj:=j.isLt;omega
  | serreELeft i j hij => have hi:=i.isLt;have hj:=j.isLt;omega
  | serreERight i j hij => have hi:=i.isLt;have hj:=j.isLt;omega
  | serreFLeft i j hij => have hi:=i.isLt;have hj:=j.isLt;omega
  | serreFRight i j hij => have hi:=i.isLt;have hj:=j.isLt;omega

def rankTwoToSL2 (q : K) : UqTypeA q 1 →ₐ[K] UqSL2 q :=
  RingQuot.liftAlgHom K ⟨rankTwoToSL2Free q,by intro x y h;exact rankTwoToSL2Free_respects q h⟩

theorem rankTwoToSL2_generator (q : K) (i : Fin 1) (t : Fin 4) :
    rankTwoToSL2 q (typeAAlgebraGenerator q 1 i t)=uqGenerator q t := by
  simp [rankTwoToSL2,rankTwoToSL2Free,typeAAlgebraGenerator,typeAFreeGenerator]

def sl2ToRankTwoFree (q : K) : FreeAlgebra K (Fin 4) →ₐ[K] UqTypeA q 1 :=
  FreeAlgebra.lift K (fun t =>typeAAlgebraGenerator q 1 0 t)

theorem sl2ToRankTwoFree_respects (q : K)
    {x y : FreeAlgebra K (Fin 4)} (h : QuantumSL2Relation q x y) :
    sl2ToRankTwoFree q x=sl2ToRankTwoFree q y := by
  cases h
  · simpa [sl2ToRankTwoFree] using uqA_inverse q 1 0
  · simpa [sl2ToRankTwoFree] using uqA_inverse' q 1 0
  · simpa [sl2ToRankTwoFree,typeACartan,zpow_ofNat] using uqA_weightE q 1 0 0
  · simpa [sl2ToRankTwoFree,typeACartan,zpow_ofNat] using uqA_weightF q 1 0 0
  · simpa [sl2ToRankTwoFree] using uqA_commutator q 1 0

def sl2ToRankTwo (q : K) : UqSL2 q →ₐ[K] UqTypeA q 1 :=
  RingQuot.liftAlgHom K ⟨sl2ToRankTwoFree q,by intro x y h;exact sl2ToRankTwoFree_respects q h⟩

theorem sl2ToRankTwo_generator (q : K) (t : Fin 4) :
    sl2ToRankTwo q (uqGenerator q t)=typeAAlgebraGenerator q 1 0 t := by
  simp [sl2ToRankTwo,sl2ToRankTwoFree,uqGenerator]

theorem rankTwoToSL2_left_inverse (q : K) :
    (sl2ToRankTwo q).comp (rankTwoToSL2 q)=AlgHom.id K (UqTypeA q 1) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  change sl2ToRankTwo q (rankTwoToSL2 q (typeAAlgebraGenerator q 1 it.1 it.2))=_
  rw [rankTwoToSL2_generator,sl2ToRankTwo_generator]
  congr 1
  exact Subsingleton.elim _ _

theorem rankTwoToSL2_right_inverse (q : K) :
    (rankTwoToSL2 q).comp (sl2ToRankTwo q)=AlgHom.id K (UqSL2 q) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext t
  change rankTwoToSL2 q (sl2ToRankTwo q (uqGenerator q t))=_
  rw [sl2ToRankTwo_generator,rankTwoToSL2_generator]
  rfl

/-- The independently presented type-A rank-one and standard sl2 algebras
are explicitly isomorphic, with matching E,F,K,Ki generators. -/
def rankTwoSL2Equiv (q : K) : UqTypeA q 1 ≃ₐ[K] UqSL2 q :=
  AlgEquiv.ofAlgHom (rankTwoToSL2 q) (sl2ToRankTwo q)
    (rankTwoToSL2_right_inverse q) (rankTwoToSL2_left_inverse q)

end AMSPhysical
#print axioms AMSPhysical.rankTwoSL2Equiv
