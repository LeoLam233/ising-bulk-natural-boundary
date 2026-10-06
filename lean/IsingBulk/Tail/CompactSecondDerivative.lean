import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Real second-chain rule used for smooth coupled angular paths. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology

 theorem second_derivative_comp_curve {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : ℝ → E} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f (p x)) (hp : ContDiffAt ℝ 2 p x) :
    deriv (deriv (fun t => f (p t))) x =
      iteratedFDeriv ℝ 2 f (p x) (fun _ => deriv p x)+
        fderiv ℝ f (p x) (deriv (deriv p) x) := by
  have hp' : DifferentiableAt ℝ p x := hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) (p x) := hf.fderiv_right (by norm_num)
  have hpd : ContDiffAt ℝ 1 (deriv p) x := hp.derivWithin (by norm_num)
  have hd := (hfd.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hp'.hasDerivAt
  have hsecond := hd.clm_apply (hpd.differentiableAt (by norm_num)).hasDerivAt
  have he : deriv (fun t => f (p t)) =ᶠ[𝓝 x]
      (fun t => (fderiv ℝ f (p t)) (deriv p t)) := by
    filter_upwards [hp.eventually (by norm_num),hp.continuousAt.eventually (hf.eventually (by norm_num))] with t ht hf'
    exact ((hf'.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hh := (hsecond.congr_of_eventuallyEq he).deriv
  simpa only [iteratedFDeriv_two_apply,Function.comp_apply] using hh


/-- Quantitative second-chain stability. The actual source attachments
provide the four jet bounds; this algebraic lemma never assumes a Hessian
sign or a source-sector estimate. -/
theorem second_derivative_curve_perturbation {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : ℝ → E} {x : ℝ} (q e : E)
    (hf : ContDiffAt ℝ 2 f (p x)) (hp : ContDiffAt ℝ 2 p x)
    {B δ U V T : ℝ} (hB : 0≤B) (hδ : 0≤δ) (hU : 1≤U) (_hV : 0≤V) (_hT : 0≤T)
    (hfirst : ‖fderiv ℝ f (p x)‖≤B) (hsecond : ‖iteratedFDeriv ℝ 2 f q‖≤B)
    (hmotion : ‖iteratedFDeriv ℝ 2 f (p x)-iteratedFDeriv ℝ 2 f q‖≤δ)
    (hvelocity : ‖deriv p x‖≤U) (hbase : ‖e‖≤1)
    (hvelocityDiff : ‖deriv p x-e‖≤V) (haccel : ‖deriv (deriv p) x‖≤T) :
    ‖deriv (deriv (fun t => f (p t))) x-iteratedFDeriv ℝ 2 f q (fun _ => e)‖≤
      δ*U^2+2*B*U*V+B*T := by
  let H := iteratedFDeriv ℝ 2 f (p x)
  let H₀ := iteratedFDeriv ℝ 2 f q
  let u := deriv p x
  have hU0 : 0≤U := by linarith
  have hdiff : ‖(H-H₀) (fun _ => u)‖≤δ*U^2 := by
    have hh := (H-H₀).le_opNorm (fun _ => u)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul hmotion (pow_le_pow_left₀ (norm_nonneg _) hvelocity 2)
      (by positivity) hδ)
  have hmove : ‖H₀ (fun _ => u)-H₀ (fun _ => e)‖≤2*B*U*V := by
    have hh := H₀.norm_image_sub_le (fun _ => u) (fun _ => e)
    have hn : ‖(fun _ : Fin 2 => u)‖=‖u‖ := by simp
    have hn' : ‖(fun _ : Fin 2 => e)‖=‖e‖ := by simp
    have hd : ‖(fun _ : Fin 2 => u)-(fun _ : Fin 2 => e)‖=‖u-e‖ := by
      change ‖(fun _ : Fin 2 => u-e)‖=‖u-e‖
      simp
    rw [hn,hn',hd] at hh
    norm_num only [Fintype.card_fin, Nat.reduceSub,pow_one] at hh
    have hmax : max ‖u‖ ‖e‖≤U := max_le hvelocity (hbase.trans hU)
    calc
      _ ≤ ‖H₀‖*2*max ‖u‖ ‖e‖*‖u-e‖ := hh
      _ ≤ B*2*U*V := by gcongr
      _ = _ := by ring
  have hacc : ‖fderiv ℝ f (p x) (deriv (deriv p) x)‖≤B*T :=
    ((fderiv ℝ f (p x)).le_opNorm _).trans (mul_le_mul hfirst haccel (norm_nonneg _) hB)
  rw [second_derivative_comp_curve hf hp]
  have he : H (fun _ => u)+fderiv ℝ f (p x) (deriv (deriv p) x)-H₀ (fun _ => e)=
      ((H-H₀) (fun _ => u)+(H₀ (fun _ => u)-H₀ (fun _ => e)))+
        fderiv ℝ f (p x) (deriv (deriv p) x) := by
    simp only [sub_apply]
    abel
  change ‖H (fun _ => u)+fderiv ℝ f (p x) (deriv (deriv p) x)-H₀ (fun _ => e)‖≤_
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hdiff hmove)) hacc)

end
end IsingBulk.Tail
