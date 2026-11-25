import QuantumCupBoundaryDiagonal
import QuantumTripleCreationShifts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def cupFirstBoundaryPoint (n : ℕ) (l h c : ℤ) (t k : ℕ) : OccupationTripleLattice n :=
  (Pi.single 0 l, Pi.single 0 ((t:ℤ)+(k:ℤ))+Pi.single (Fin.last n) h, Pi.single 0 c)

/-- At a pure highest third symmetric occupation, only creation at coordinate
zero can contribute. This fixes the literal reversed-cup sign. -/
theorem tripleRightCreation_third_first_boundary (q : ℝ) (n : ℕ) (c : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f)
    (x y : Fin (n+1) → ℤ) :
    tripleRightCreation q n f (x,y+Pi.single 0 1,Pi.single 0 (c+1)) =
      ((-1:ℝ)^n*q^(-(n:ℤ)-(∑ i,y i)-c))*f (x,y,Pi.single 0 c) := by
  classical
  simp only [tripleRightCreation,LinearMap.sum_apply,Finsupp.finset_sum_apply,weightedTranslation_apply]
  rw [Finset.sum_eq_single (0:Fin (n+1))]
  · have he : (x,y+Pi.single 0 1,Pi.single 0 (c+1))-tripleRightCreationShift n 0 =
        (x,y,Pi.single 0 c) := by
      ext i <;> simp [tripleRightCreationShift,Pi.single_apply] <;> split_ifs <;> ring
    rw [he]
    simp only [tripleRightCreationCoefficient, mixedCreationCoefficient, Fin.rev_zero, Fin.val_last,
      occupationPrefix_last_sum, occupationLatticeReflect_sum]
    simp only [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro j hj hj0
    have he : ((x,y+Pi.single 0 1,Pi.single 0 (c+1))-tripleRightCreationShift n j).2.2 j = -1 := by
      simp [tripleRightCreationShift,Pi.single_apply,hj0,Ne.symm hj0]
    have hz : f ((x,y+Pi.single 0 1,Pi.single 0 (c+1))-tripleRightCreationShift n j)=0 := by
      by_contra hc
      have hp:=(hf _ hc).2.2 j
      rw [he] at hp
      omega
    rw [hz,zero_mul]
  · simp

theorem tripleRightCreation_power_third_first_boundary (q : ℝ) (hq : q≠0) (n : ℕ) (c : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientSupported (tripleOccupationNonnegative n) f)
    (x y : Fin (n+1) → ℤ) (k : ℕ) :
    ((tripleRightCreation q n)^k) f (x,y+Pi.single 0 (k:ℤ),Pi.single 0 (c+(k:ℤ))) =
      ((-1:ℝ)^(n*k)*q^(-((n:ℤ)+(∑ i,y i)+c)*(k:ℤ)-(k:ℤ)^2+(k:ℤ)))*
        f (x,y,Pi.single 0 c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : ((tripleRightCreation q n)^(k+1)) f =
        tripleRightCreation q n (((tripleRightCreation q n)^k) f) :=
      DFunLike.congr_fun (pow_succ' (tripleRightCreation q n) k) f
    have hpoint : ((x,y+Pi.single 0 ((k+1:ℕ):ℤ),Pi.single 0 (c+((k+1:ℕ):ℤ))) : OccupationTripleLattice n) =
        (x,(y+Pi.single 0 (k:ℤ))+Pi.single 0 1,Pi.single 0 ((c+(k:ℤ))+1)) := by
      ext i <;> simp [Pi.single_apply] <;> split_ifs <;> push_cast <;> ring
    rw [hp,hpoint,tripleRightCreation_third_first_boundary q n (c+(k:ℤ)) _
      (coefficientSupported_pow (tripleOccupationNonnegative n) (tripleRightCreation q n)
        (tripleRightCreation_nonnegative_support q n) f hf k),ih]
    simp only [Pi.add_apply,Finset.sum_add_distrib,Pi.single_apply,Finset.sum_ite_eq',
      Finset.mem_univ,if_true,Nat.mul_add,Nat.mul_one,pow_add]
    have hexp : (-(n:ℤ)-((∑ i,y i)+(k:ℤ))-(c+(k:ℤ)))+
        (-((n:ℤ)+(∑ i,y i)+c)*(k:ℤ)-(k:ℤ)^2+(k:ℤ)) =
        -((n:ℤ)+(∑ i,y i)+c)*((k+1:ℕ):ℤ)-((k+1:ℕ):ℤ)^2+((k+1:ℕ):ℤ) := by
      push_cast;ring
    calc
      _ = ((-1:ℝ)^(n*k)*(-1:ℝ)^n)*
        (q^(-(n:ℤ)-((∑ i,y i)+(k:ℤ))-(c+(k:ℤ)))*
          q^(-((n:ℤ)+(∑ i,y i)+c)*(k:ℤ)-(k:ℤ)^2+(k:ℤ)))*
            f (x,y,Pi.single 0 c) := by ring
      _ = _ := by rw [← zpow_add₀ hq,hexp]

/-- Complete one-path value at the all-first-coordinate boundary. Its
phase is (-1)^(n*k); the remaining factor is positive for positive q. -/
theorem quantumCupMonomial_first_boundary (q : ℝ) (hq : q≠0) (n : ℕ) (hn : 0<n)
    (l h c : ℤ) (t k : ℕ) (hl : (t:ℤ)≤l) (hh : 0≤h) (hc : (k:ℤ)≤c) :
    quantumCupMonomial q n l h c t k (cupFirstBoundaryPoint n l h c t k) =
      (-1:ℝ)^(n*k)*q^((t:ℤ)*(1-l-(k:ℤ))+(k:ℤ)*(1-(n:ℤ)-h-c)) := by
  have hn0 : (Fin.last n : Fin (n+1))≠0 := by
    intro he;have hs:=congrArg Fin.val he
    simp only [Fin.val_last,Fin.val_zero] at hs;omega
  have hf:=tripleCupBase_nonnegative_support n (l-(t:ℤ)) h (c-(k:ℤ)) (by omega) hh (by omega)
  have hR:=tripleRightCreation_power_third_first_boundary q hq n (c-(k:ℤ))
    (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ))) hf
    (Pi.single 0 (l-(t:ℤ))) (Pi.single (Fin.last n) h) k
  simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hR
  rw [show tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ))
    (Pi.single 0 (l-(t:ℤ)),Pi.single (Fin.last n) h,Pi.single 0 (c-(k:ℤ)))=1 by simp [tripleCupBase],mul_one] at hR
  have hL:=tripleLeftCreation_power_first_boundary q hq n (l-(t:ℤ))
    (((tripleRightCreation q n)^k) (tripleCupBase n (l-(t:ℤ)) h (c-(k:ℤ))))
    (coefficientSupported_pow (tripleOccupationNonnegative n) (tripleRightCreation q n)
      (tripleRightCreation_nonnegative_support q n) _ hf k)
    (Pi.single (Fin.last n) h+Pi.single 0 (k:ℤ)) (Pi.single 0 (c-(k:ℤ)+(k:ℤ))) t
  have hy : (Pi.single (Fin.last n) h+Pi.single 0 (k:ℤ) : Fin (n+1) → ℤ) 0=(k:ℤ) := by
    simp [Pi.single_apply,Ne.symm hn0]
  rw [hy,hR] at hL
  have hp : ((Pi.single 0 (l-(t:ℤ)+(t:ℤ)),
      (Pi.single (Fin.last n) h+Pi.single 0 (k:ℤ))+Pi.single 0 (t:ℤ),
      Pi.single 0 (c-(k:ℤ)+(k:ℤ))) : OccupationTripleLattice n) = cupFirstBoundaryPoint n l h c t k := by
    ext i <;> simp [cupFirstBoundaryPoint,Pi.single_apply] <;> split_ifs <;> ring
  rw [hp] at hL
  change quantumCupMonomial q n l h c t k (cupFirstBoundaryPoint n l h c t k)=_ at hL
  calc
    _ = _ := hL
    _ = (-1:ℝ)^(n*k)*
      (q^(-(l-(t:ℤ)+(k:ℤ))*(t:ℤ)-(t:ℤ)^2+(t:ℤ))*
        q^(-((n:ℤ)+h+(c-(k:ℤ)))*(k:ℤ)-(k:ℤ)^2+(k:ℤ))) := by ring
    _ = _ := by rw [← zpow_add₀ hq];congr 2;ring

end AMSPhysical
#print axioms AMSPhysical.quantumCupMonomial_first_boundary
