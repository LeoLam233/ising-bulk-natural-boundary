import IsingBulk.AnisoF002.C03.RegularCollisionBlowup
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# The filled scaled physical kernel and complete density

At a true resonance the physical site denominator has the exact s²
factor of the full phase sum.  The exponential divided difference fills
that factor.  Combined with the actual Vandermonde factorization this
gives one jointly analytic scaled complete density and all its parameter
derivatives, including the s=0 value needed in the first-amplitude limit.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def collisionBlowupKernel {N : ℕ} (b : ℝ) (a : ℂ → ℂ) (x : Fin N → ℂ)
    (p : ℂ × ℂ) : ℂ :=
  (1 + Complex.exp (-(p.1 ^ 2 * collisionBlowupTotal b a x p))) /
    (collisionBlowupTotal b a x p *
      dslope Complex.exp 0 (-(p.1 ^ 2 * collisionBlowupTotal b a x p)))

def collisionBlowupDensity {N : ℕ} (b : ℝ) (a : ℂ → ℂ) (x : Fin N → ℂ)
    (p : ℂ × ℂ) : ℂ :=
  edgeVandermondeSquared x *
    edgeCollisionNumerator (affineEdgeCenter b) a (p.1 ^ 2 * p.2, fun i => p.1 * x i) *
      collisionBlowupKernel b a x p

theorem phaseSiteFactor_scaled_exact (G Γ s : ℂ) (hs : s ≠ 0)
    (hres : Complex.exp (-Γ) = 1) :
    s ^ 2 * phaseSiteFactor (Γ + s ^ 2 * G) =
      (1 + Complex.exp (-(s ^ 2 * G))) /
        (G * dslope Complex.exp 0 (-(s ^ 2 * G))) := by
  have hd := sub_smul_dslope Complex.exp 0 (-(s ^ 2 * G))
  simp only [sub_zero, Complex.exp_zero, smul_eq_mul] at hd
  have he : 1 - Complex.exp (-(s ^ 2 * G)) =
      s ^ 2 * (G * dslope Complex.exp 0 (-(s ^ 2 * G))) := by
    linear_combination hd
  unfold phaseSiteFactor
  rw [neg_add, Complex.exp_add, hres, one_mul, he, ← mul_div_assoc,
    mul_div_mul_left _ _ (pow_ne_zero 2 hs)]

theorem edgeVandermondeSquared_scaling {N : ℕ} (x : Fin N → ℂ) (s : ℂ) :
    edgeVandermondeSquared (fun i => s * x i) =
      s ^ (2 * N.choose 2) * edgeVandermondeSquared x := by
  unfold edgeVandermondeSquared
  simp_rw [← mul_sub, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_indexPairs, ← pow_mul]

theorem collisionBlowupDensity_exact {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (s t : ℂ) (hs : s ≠ 0)
    (hres : upperEdgeRoot (b : ℂ) ^ N = 1) :
    s ^ 2 * edgeJointDensity (affineEdgeCenter b) a (s ^ 2 * t, fun i => s * x i) =
      s ^ (2 * N.choose 2) * collisionBlowupDensity b a x (s, t) := by
  have hΓ := collisionBlowupTotal_exact b a x s t
  have hΓ' : edgeJointTotalPhase (affineEdgeCenter b) a (s ^ 2 * t, fun i => s * x i) =
      (N : ℂ) * upperEdgePhase (b : ℂ) + s ^ 2 * collisionBlowupTotal b a x (s, t) := by
    linear_combination hΓ
  have hr : Complex.exp (-((N : ℂ) * upperEdgePhase (b : ℂ))) = 1 := by
    rw [show -((N : ℂ) * upperEdgePhase (b : ℂ)) =
      (N : ℂ) * (-upperEdgePhase (b : ℂ)) by ring, Complex.exp_nat_mul,
      upperEdgePhase_exp_neg, hres]
  have hk := phaseSiteFactor_scaled_exact (collisionBlowupTotal b a x (s, t))
    ((N : ℂ) * upperEdgePhase (b : ℂ)) s hs hr
  rw [edgeJointDensity, edgeJointNumerator_collision_factorization,
    edgeVandermondeSquared_scaling, hΓ']
  change s ^ 2 * (s ^ (2 * N.choose 2) * edgeVandermondeSquared x *
    edgeCollisionNumerator (affineEdgeCenter b) a (s ^ 2 * t, fun i => s * x i) * _) = _
  unfold collisionBlowupDensity collisionBlowupKernel
  linear_combination s ^ (2 * N.choose 2) * edgeVandermondeSquared x *
    edgeCollisionNumerator (affineEdgeCenter b) a (s ^ 2 * t, fun i => s * x i) * hk

theorem collisionBlowupKernel_center {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (t : ℂ) :
    collisionBlowupKernel b a x (0, t) = 2 / collisionBlowupTotal b a x (0, t) := by
  norm_num [collisionBlowupKernel, dslope_same, Complex.deriv_exp]

theorem collisionBlowupKernel_analytic {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : AnalyticAt ℂ a 0) (x : Fin N → ℂ) (t : ℂ)
    (hG : collisionBlowupTotal b a x (0, t) ≠ 0) :
    AnalyticAt ℂ (collisionBlowupKernel b a x) (0, t) := by
  have htot := collisionBlowupTotal_analytic hb ha x t
  have harg : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      -(p.1 ^ 2 * collisionBlowupTotal b a x p)) (0, t) :=
    ((analyticAt_fst.pow 2).mul htot).neg
  have hds0 := analyticAt_dslope_center (analyticAt_id.cexp : AnalyticAt ℂ Complex.exp 0)
  have hds := hds0.comp_of_eq harg (by simp)
  exact (analyticAt_const.add harg.cexp).div (htot.mul hds)
    (by simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, neg_zero,
      dslope_same, Complex.deriv_exp, Complex.exp_zero, mul_one] using hG)

theorem collisionBlowupDensity_center {N : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (x : Fin N → ℂ) (t : ℂ) :
    collisionBlowupDensity b a x (0, t) =
      2 * edgeVandermondeSquared x *
        edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin N → ℂ)) /
          (deriv upperEdgePhase (b : ℂ) * ((N : ℂ) * t + a 0 / 2 * ∑ i, x i ^ 2)) := by
  rw [collisionBlowupDensity, collisionBlowupKernel_center, collisionBlowupTotal_center]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, Pi.zero_def]
  ring

theorem collisionBlowupDensity_analytic {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (d : RegularEdgeControl (affineEdgeCenter b) a) (hb : |b| < 1)
    (x : Fin N → ℂ) (t : ℂ) (hG : collisionBlowupTotal b a x (0, t) ≠ 0) :
    AnalyticAt ℂ (collisionBlowupDensity b a x) (0, t) := by
  have ht0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) d.radius :=
    Metric.mem_closedBall_self d.radius_pos.le
  have hnum : AnalyticAt ℂ (edgeCollisionNumerator (affineEdgeCenter b) a)
      ((0 : ℂ), (0 : Fin N → ℂ)) := by
    apply d.collisionNumerator_analytic ht0
    intro i
    simp only [Pi.zero_apply, Complex.cos_zero]
    exact Metric.self_subset_thickening d.cosineRadius_pos _
      (by refine ⟨1, by norm_num, by simp⟩)
  have hmap : AnalyticAt ℂ (fun p : ℂ × ℂ => (p.1 ^ 2 * p.2, fun i => p.1 * x i)) (0, t) :=
    ((analyticAt_fst.pow 2).mul analyticAt_snd).prod
      (AnalyticAt.pi fun i => analyticAt_fst.mul analyticAt_const)
  exact (analyticAt_const.mul (hnum.comp_of_eq hmap (by simp [Pi.zero_def]))).mul
    (collisionBlowupKernel_analytic hb (d.coefficient_analytic 0 ht0) x t hG)

theorem iteratedDeriv_comp_mul_unconditional (j : ℕ) (f : ℂ → ℂ) (c t : ℂ) :
    iteratedDeriv j (fun u => f (c * u)) t = c ^ j * iteratedDeriv j f (c * t) := by
  induction j generalizing f t with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, show (iteratedDeriv j (fun u => f (c * u))) =
      (fun u => c ^ j * iteratedDeriv j f (c * u)) by funext u; exact ih f u,
      deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, iteratedDeriv_succ]
    ring

theorem second_parameter_jet_continuous {f : ℂ × ℂ → ℂ} {s t : ℂ}
    (hf : AnalyticAt ℂ f (s, t)) (j : ℕ) :
    ContinuousAt (fun v => iteratedDeriv j (fun u => f (v, u)) t) s := by
  have hswap : AnalyticAt ℂ (fun p : ℂ × ℂ => f (p.2, p.1)) (t, s) :=
    hf.comp (f := fun p : ℂ × ℂ => (p.2, p.1)) (analyticAt_snd.prod analyticAt_fst)
  exact (parameterIteratedDeriv_analyticAt hswap j).continuousAt.comp
    (f := fun v : ℂ => (t, v)) (continuousAt_const.prodMk continuousAt_id)

end
end IsingBulk.AnisoF002.RegularTail.C03
