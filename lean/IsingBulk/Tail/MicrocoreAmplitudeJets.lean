import IsingBulk.Tail.MicrocoreDensity
import IsingBulk.Analysis.JetsScalarBounds

/-! Uniform scalar analytic jet inputs and product budgets for the actual
microcore amplitude. Constants are chosen before the particle number. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Filter
open scoped BigOperators Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

 theorem microRegularOneBody_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹=(1+c:ℂ)) (hc : |c|<1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => microRegularOneBody z.1 z.2) (s,0) := by
  have hy := regularY_analytic_base s c hs hS hc
  have hd : 1-((regularY s 0)^2)⁻¹ ≠ 0 := by
    simpa only [pow_two] using regularY_base_denominator s c hS hc
  have hden : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      (Real.pi:ℂ)*(1-((regularY z.1 z.2)^2)⁻¹)) (s,0) :=
    analyticAt_const.mul (analyticAt_const.sub ((hy.pow 2).inv (pow_ne_zero 2 (regularY_ne_zero s 0))))
  have hnum : AnalyticAt ℂ (fun z : ℂ × ℂ => -Complex.exp (-Complex.I*z.2)) (s,0) := by fun_prop
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  convert! hnum.div hden (mul_ne_zero hpi hd) using 1

 def microScalarFactor (i : Fin 4) (z : ℂ × ℂ) : ℂ :=
  if i=0 then microRegularOneBody z.1 z.2 else
  if i=1 then (regularY z.1 z.2)⁻¹ else
  if i=2 then Complex.exp (Complex.I*z.2) else regularA z.1 z.2

 theorem microScalarFactor_analytic_base (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹=(1+c:ℂ)) (hc : |c|<1) (i : Fin 4) :
    AnalyticAt ℂ (microScalarFactor i) (s,0) := by
  fin_cases i
  · change AnalyticAt ℂ (fun z : ℂ × ℂ => microRegularOneBody z.1 z.2) (s,0)
    exact microRegularOneBody_analytic_base s c hs hS hc
  · change AnalyticAt ℂ (fun z : ℂ × ℂ => (regularY z.1 z.2)⁻¹) (s,0)
    exact (regularY_analytic_base s c hs hS hc).inv (regularY_ne_zero s 0)
  · change AnalyticAt ℂ (fun z : ℂ × ℂ => Complex.exp (Complex.I*z.2)) (s,0)
    fun_prop
  · change AnalyticAt ℂ (fun z : ℂ × ℂ => regularA z.1 z.2) (s,0)
    exact regularA_analytic_base s c hs hS hc

 theorem micro_scalar_jets_uniform (s : ℂ) (c : ℝ) (hs : s ≠ 0)
    (hS : s+s⁻¹=(1+c:ℂ)) (hc : |c|<1) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ z in 𝓝 (s,0), ∀ i : Fin 4,
      JetBound (microScalarFactor i) z J C :=
  finite_family_jet_bounds microScalarFactor (s,0)
    (microScalarFactor_analytic_base s c hs hS hc) J

/-- Finite products cost one 2^J per multiplication, hence exponential in
number of factors. Applied to O(N²) source factors this is exp(O_J(N²)). -/
 theorem jetBound_finset_product {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [DecidableEq ι] (S : Finset ι) (f : ι → E → ℂ) (z : E) (J : ℕ) (C : ℝ)
    (h : ∀ i ∈ S, JetBound (f i) z J C) :
    JetBound (fun y => ∏ i ∈ S, f i y) z J ((2^J*C)^S.card) := by
  induction S using Finset.induction_on with
  | empty => simpa using JetBound.const (1:ℂ) z J
  | @insert i S hi ih =>
    have hf := h i (Finset.mem_insert_self _ _)
    have hg := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    have hh := hf.mul hg
    have he : 2^J*C*(2^J*C)^S.card=(2^J*C)^(S.card+1) := by rw [pow_succ]; ring
    simpa only [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,he] using hh

end
end IsingBulk.Tail
