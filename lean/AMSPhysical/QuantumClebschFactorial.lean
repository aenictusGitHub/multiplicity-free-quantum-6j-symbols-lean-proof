import QuantumClebschSingleSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def clebschFactorialTerm (q : ℝ) (l m r a u k : ℕ) : ℝ :=
  (-1:ℝ)^k*q^((k:ℤ)*((a:ℤ)-(coupledLabel l m r:ℤ)-1))*qfactorial q (l-k)*qfactorial q (m-r+k)/
    (qfactorial q k*qfactorial q (r-k)*qfactorial q (descendantIndex a k u)*
      qfactorial q (a-descendantIndex a k u))

def clebschFactorialSum (q : ℝ) (l m r a u : ℕ) : ℝ :=
  ∑ k∈Finset.range (r+1),if DescendantAdmissible a k u then clebschFactorialTerm q l m r a u k else 0

def clebschExpansionPrefactor (q : ℝ) (l m r a u v : ℕ) : ℝ :=
  q^(((a:ℤ)-(u:ℤ))*((u:ℤ)-(l:ℤ)))*qfactorial q r*qfactorial q a/
    (qfactorial q (l-u)*qfactorial q (m-v))

theorem clebschSingleTerm_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m r a u v k : ℕ) (hl : r≤l) (hm : r≤m) (hu : u≤l) (hv : v≤m)
    (huv : u+v=r+a) (hk : k≤r) (hadm : DescendantAdmissible a k u) :
    clebschSingleTerm q l m r a k (descendantIndex a k u)=
      clebschExpansionPrefactor q l m r a u v*clebschFactorialTerm q l m r a u k := by
  let t := descendantIndex a k u
  have hti : (t:ℤ)=(k:ℤ)+(a:ℤ)-(u:ℤ) := by
    dsimp [t,descendantIndex]
    have hh := hadm.1
    omega
  have hta : t≤a := by have hh := hadm.2;omega
  have hku : k≤u := by have hh := hadm.2;omega
  have hA : a-t≤l-k := by omega
  have hB : t≤m-r+k := by omega
  have hsubA : l-k-(a-t)=l-u := by omega
  have hsubB : m-r+k-t=m-v := by omega
  have hcastA : (l:ℤ)-(k:ℤ)=((l-k:ℕ):ℤ) := by omega
  have hcastB : (m:ℤ)-(r:ℤ)+(k:ℤ)=((m-r+k:ℕ):ℤ) := by omega
  have hphase : q^(couplingExponent (m:ℤ) r k)*q^((t*(a-t):ℕ):ℤ)*
      q^(-(t:ℤ)*((l:ℤ)-2*(k:ℤ)))=
      q^(((a:ℤ)-(u:ℤ))*((u:ℤ)-(l:ℤ)))*q^((k:ℤ)*((a:ℤ)-(coupledLabel l m r:ℤ)-1)) := by
    rw [← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    have hat : ((a-t:ℕ):ℤ)=(a:ℤ)-(t:ℤ) := by omega
    simp only [couplingExponent,Nat.cast_mul]
    rw [hat,hti,coupledLabel_cast l m r hl hm]
    ring
  change clebschSingleTerm q l m r a k t=_
  unfold clebschSingleTerm
  rw [couplingCoefficient_factorial q hq hq1 _ r k hk,gaussianBinomial_factorial q hq a t hta,
    hcastA,hcastB,qFalling_factorial q hq hq1 (l-k) (a-t) hA,
    qFalling_factorial q hq hq1 (m-r+k) t hB,hsubA,hsubB]
  unfold clebschExpansionPrefactor clebschFactorialTerm
  change _=q^(((a:ℤ)-(u:ℤ))*((u:ℤ)-(l:ℤ)))*qfactorial q r*qfactorial q a/
    (qfactorial q (l-u)*qfactorial q (m-v))*
    ((-1:ℝ)^k*q^((k:ℤ)*((a:ℤ)-(coupledLabel l m r:ℤ)-1))*qfactorial q (l-k)*qfactorial q (m-r+k)/
      (qfactorial q k*qfactorial q (r-k)*qfactorial q t*qfactorial q (a-t)))
  simp only [div_eq_mul_inv,mul_inv_rev]
  linear_combination
    ((-1:ℝ)^k*qfactorial q r*qfactorial q a*qfactorial q (l-k)*qfactorial q (m-r+k)*
      (qfactorial q k)⁻¹*(qfactorial q (r-k))⁻¹*(qfactorial q t)⁻¹*(qfactorial q (a-t))⁻¹*
      (qfactorial q (l-u))⁻¹*(qfactorial q (m-v))⁻¹)*hphase

theorem clebschSingleSum_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m r a u v : ℕ) (hl : r≤l) (hm : r≤m) (hu : u≤l) (hv : v≤m) (huv : u+v=r+a) :
    clebschSingleSum q l m r a u=clebschExpansionPrefactor q l m r a u v*clebschFactorialSum q l m r a u := by
  unfold clebschSingleSum clebschFactorialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hadm : DescendantAdmissible a k u
  · rw [if_pos hadm,if_pos hadm]
    exact clebschSingleTerm_factorial q hq hq1 l m r a u v k hl hm hu hv huv
      (by have hh := Finset.mem_range.mp hk;omega) hadm
  · rw [if_neg hadm,if_neg hadm,mul_zero]

/-- Explicit factorial expression, defined independently and identified with the actual CG map below. -/
def regularClebschFactorialCoefficient (q : ℝ) (l m r a u v : ℕ) : ℝ :=
  (Real.sqrt (couplingNormClosed q (l-r) (m-r) r))⁻¹*
    q^(((a:ℤ)-(u:ℤ))*((u:ℤ)-(l:ℤ)))*qfactorial q r*qfactorial q a*qfactorial q (coupledLabel l m r-a)/
    (qfactorial q (coupledLabel l m r)*qfactorial q (l-u)*qfactorial q (m-v))*
      clebschFactorialSum q l m r a u

/-- The factorial one-sum is proved equal to the independently constructed isometric CG coefficient. -/
theorem standardClebschCoefficient_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (u v : ℕ)
    (hu : u≤l) (hv : v≤m) (huv : u+v=r.val+a.val) :
    standardClebschCoefficient q hq hq1 l m r a (u:ℤ) (v:ℤ)=
      regularClebschFactorialCoefficient q l m r.val a.val u v := by
  have hsum : (u:ℤ)+(v:ℤ)=(r.val:ℤ)+(a.val:ℤ) := by exact_mod_cast huv
  rw [standardClebschCoefficient_singleSum q hq hq1 l m r a u v hsum,
    clebschSingleSum_factorial q hq hq1 l m r.val a.val u v
      (channel_left_bound l m r) (channel_right_bound l m r) hu hv huv,
    qFalling_factorial q hq hq1 (coupledLabel l m r) a.val (by have hh := a.isLt;omega)]
  unfold regularClebschFactorialCoefficient clebschExpansionPrefactor
  rw [inv_div]
  ring

end AMSPhysical

#print axioms AMSPhysical.clebschSingleSum_factorial

#print axioms AMSPhysical.standardClebschCoefficient_factorial
