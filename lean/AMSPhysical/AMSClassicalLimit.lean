import AMSAnalyticRegularity
import PhysicalTypeIIExactAMS

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open Set Filter
open scoped Topology

def ordinaryThetaSq (h:ℕ) (a b c:ℤ):ℝ:=
  (((a+b-c)/2).toNat.factorial:ℝ)*(((a+c-b)/2).toNat.factorial:ℝ)*
    (((b+c-a)/2).toNat.factorial:ℝ)/(((a+b+c)/2+h+1).toNat.factorial:ℝ)

def ordinaryFourTrianglePrefactor (h:ℕ) (a b c d i j:ℤ):ℝ:=
  ((h+1).factorial:ℝ)*(h.factorial:ℝ)*Real.sqrt
    (ordinaryThetaSq h a b i*ordinaryThetaSq h c d i*ordinaryThetaSq h a d j*ordinaryThetaSq h b c j)

theorem amsThetaSq_at_one (h:ℕ) (a b c:ℤ):amsThetaSq 1 h a b c=ordinaryThetaSq h a b c:=by
  simp only [amsThetaSq,ordinaryThetaSq,quantumFactorialInt_at_one]

theorem amsFourTrianglePrefactor_at_one (h:ℕ) (a b c d i j:ℤ):
    amsFourTrianglePrefactor 1 h a b c d i j=ordinaryFourTrianglePrefactor h a b c d i j:=by
  simp only [amsFourTrianglePrefactor,factorialConstant,qfactorial_at_one,amsThetaSq_at_one,
    ordinaryFourTrianglePrefactor]

/-- A general limit principle for already-proved physical coefficients.
The physical family is an independent input; equality away from one and
proved regularity imply its actual punctured limit, with ordinary factorials. -/
theorem physicalAMS_limit_at_one (h:ℕ) (typeII:Bool) (a b c d i j:ℤ) (f:ℝ → ℝ)
    (hf:∀ q:ℝ,0<q → q≠1 → f q=amsFourTrianglePrefactor q h a b c d i j*
      AMSGeneral.kernel (quantumFactorialInt q) h typeII a b c d i j):
    Tendsto f (𝓝[≠] (1:ℝ)) (𝓝 (ordinaryFourTrianglePrefactor h a b c d i j*
      AMSGeneral.kernel (fun z:ℤ=>(z.toNat.factorial:ℝ)) h typeII a b c d i j)) := by
  have hc:ContinuousAt (fun q:ℝ=>amsFourTrianglePrefactor q h a b c d i j*
      AMSGeneral.kernel (quantumFactorialInt q) h typeII a b c d i j) 1:=
    (amsExpression_analytic h typeII a b c d i j 1 (by norm_num)).continuousAt
  have ht:=hc.tendsto.mono_left (nhdsWithin_le_nhds:𝓝[≠] (1:ℝ)≤𝓝 1)
  have hF:quantumFactorialInt 1=(fun z:ℤ=>(z.toNat.factorial:ℝ)):=
    funext quantumFactorialInt_at_one
  rw [amsFourTrianglePrefactor_at_one,hF] at ht
  apply ht.congr'
  have hp:∀ᶠ q:ℝ in 𝓝[≠] (1:ℝ),0<q:=
    (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp,self_mem_nhdsWithin] with q hq hq1
  exact (hf q hq hq1).symm

/-- This function evaluates the actual Type-II physical coefficient wherever
its independently constructed representation is defined; the value outside
that domain is irrelevant to the punctured physical limit at one. -/
def physicalTypeIIWignerFunction (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b) (q:ℝ):ℝ:=
  if hq:0<q ∧ q≠1 then physicalTypeIICalibratedWignerSymbol q hq.1 hq.2 h a b c d hbal r t else 0

theorem physicalTypeII_AMS_q_one_limit (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    Tendsto (physicalTypeIIWignerFunction h a b c d hbal r t) (𝓝[≠] (1:ℝ))
      (𝓝 (ordinaryFourTrianglePrefactor h (a:ℤ) b c d
        (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
        AMSGeneral.kernel (fun z:ℤ=>(z.toNat.factorial:ℝ)) h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val))) := by
  apply physicalAMS_limit_at_one
  intro q hq hq1
  rw [physicalTypeIIWignerFunction,dif_pos ⟨hq,hq1⟩]
  exact physicalTypeII_AMS_Eq35_calibrated q hq hq1 h a b c d hbal r t

def physicalTypeIWignerFunction (h l m c:ℕ) (hadm:m≤l+c)
    (s t:QuantumCupIndex l m c) (q:ℝ):ℝ:=
  if hq:0<q ∧ q≠1 then physicalTypeIWignerSymbol q hq.1 hq.2 h l m c hadm s t else 0

theorem physicalTypeI_AMS_q_one_limit (h l m c:ℕ) (hadm:m≤l+c) (s t:QuantumCupIndex l m c):
    Tendsto (physicalTypeIWignerFunction h l m c hadm s t) (𝓝[≠] (1:ℝ))
      (𝓝 (ordinaryFourTrianglePrefactor h (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
        AMSGeneral.kernel (fun z:ℤ=>(z.toNat.factorial:ℝ)) h false (l:ℤ) m c (l+c-m)
          (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val))) := by
  apply physicalAMS_limit_at_one
  intro q hq hq1
  rw [physicalTypeIWignerFunction,dif_pos ⟨hq,hq1⟩]
  exact physicalTypeI_AMS_Eq35_four_triangles q hq hq1 h l m c hadm s t

end AMSPhysical
#print axioms AMSPhysical.physicalTypeII_AMS_q_one_limit
#print axioms AMSPhysical.physicalTypeI_AMS_q_one_limit
