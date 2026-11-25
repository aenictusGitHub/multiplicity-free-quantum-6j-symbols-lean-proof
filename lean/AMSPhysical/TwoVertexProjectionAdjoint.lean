import TwoVertexProjection
import TwoVertexIsometry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]

theorem weightedBasis_pair_left (b : Module.Basis I ℝ V) (w : I → ℝ) (i : I) (v : V) :
    finiteWeightedPair w b.equivFun.toLinearMap (b i) v=w i*b.equivFun v i := by
  classical
  simp [finiteWeightedPair,Module.Basis.equivFun_apply,Module.Basis.repr_self,Finsupp.single_apply]

theorem twoVertexProjection_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (L : ℕ) (v : finiteWeightSpace (K:=ℝ) L)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationCompactBilin q n L (twoVertexEmbedding n hn L v) w=
      quantumBilin q L v (twoVertexProjection n hn L w) := by
  have he : (occupationCompactBilin q n L).comp (twoVertexEmbedding n hn L)=
      (quantumBilin q L).compl₂ (twoVertexProjection n hn L) := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro i
    apply LinearMap.ext
    intro u
    change occupationCompactBilin q n L
      (twoVertexEmbedding n hn L (standardWeightBasis L i)) u=
      quantumBilin q L (standardWeightBasis L i) (twoVertexProjection n hn L u)
    rw [twoVertexEmbedding_basis]
    change finiteWeightedPair (occupationCompactWeight q n L)
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap
      (quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L i)) u=
      finiteWeightedPair (fun k : Fin (L+1) =>quantumWeight q L k.val)
        (standardWeightBasis (K:=ℝ) L).equivFun.toLinearMap (standardWeightBasis L i)
        (twoVertexProjection n hn L u)
    rw [weightedBasis_pair_left,weightedBasis_pair_left,twoVertexProjection_coordinate,twoVertexOccupation_weight q hq hq1]
  exact DFunLike.congr_fun (DFunLike.congr_fun he v) w

end AMSPhysical
#print axioms AMSPhysical.twoVertexProjection_adjoint
