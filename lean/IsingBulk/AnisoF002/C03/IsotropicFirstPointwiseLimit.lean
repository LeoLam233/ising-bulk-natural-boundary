import IsingBulk.AnisoF002.C03.IsotropicFirstBlowupDensity

/-!
# The actual isotropic first-density derivative limit

The external parameter is the original radial S increment. Joint
analyticity of the exact filling gives every derivative limit, including
its literal first amplitude, factorial, and purely imaginary quadratic
period denominator. No quadratic model replaces the physical integrand.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators
set_option maxHeartbeats 800000

theorem second_parameter_variable_jet_continuous {f : ℂ × ℂ → ℂ} {s0 t0 : ℂ}
    (hf : AnalyticAt ℂ f (s0, t0)) {T : ℂ → ℂ} (hT : ContinuousAt T s0)
    (hT0 : T s0 = t0) (j : ℕ) :
    ContinuousAt (fun s => iteratedDeriv j (fun v => f (s, v)) (T s)) s0 := by
  have hswap : AnalyticAt ℂ (fun q : ℂ × ℂ => f (q.2, q.1)) (t0, s0) :=
    hf.comp_of_eq (analyticAt_snd.prod analyticAt_fst) rfl
  have hj : AnalyticAt ℂ
      (fun q : ℂ × ℂ => iteratedDeriv j (fun v => f (q.2, v)) q.1) (t0, s0) :=
    parameterIteratedDeriv_analyticAt hswap j
  exact hj.continuousAt.comp_of_eq (hT.prodMk continuousAt_id) (Prod.ext hT0 rfl)

theorem isotropicFirstBlowupDenominator_radial_ne_zero {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℝ) :
    isotropicFirstBlowupDenominator α (fun i => (x i : ℂ))
      (0, 2 * (Real.sin α : ℂ) * Complex.I) ≠ 0 := by
  have hq : (∑ i, (x i : ℂ) ^ 2) = ((∑ i, x i ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have hd := isotropicFirstBlowupDenominator_radial_center hα hπ (fun i => (x i : ℂ)) 1
  simp only [mul_one, hq] at hd
  intro hz
  rw [hd] at hz
  have he : 2 * (N : ℂ) - Complex.I * (Real.cos α / Real.sin α : ℝ) *
      ((∑ i, x i ^ 2 : ℝ) : ℂ) =
      ((2 * (N : ℝ) : ℝ) : ℂ) -
        ((Real.cos α / Real.sin α * ∑ i, x i ^ 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he] at hz
  have hr := congrArg Complex.re hz
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.zero_re, mul_zero, zero_mul, sub_zero] at hr
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  linarith

theorem isotropicFirstScaledDensity_radial_jet_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (j : ℕ) :
    iteratedDeriv j (fun v => isotropicFirstScaledDensity α σ x (0, v))
        (2 * (Real.sin α : ℂ) * Complex.I) =
      (edgeVandermondeSquared x * isotropicFirstCenterAmplitude N α) *
        ((-1 : ℂ) ^ j * (j.factorial : ℂ) *
          (-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) ^ j /
          (2 * (N : ℂ) - Complex.I * (Real.cos α / Real.sin α : ℝ) * ∑ i, x i ^ 2) ^ (j + 1)) := by
  rw [isotropicFirstScaledDensity_jet_center hα hπ σ hres]
  have hd : (-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) *
      (2 * (Real.sin α : ℂ) * Complex.I) +
        (-Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) * ∑ i, x i ^ 2) =
      2 * (N : ℂ) - Complex.I * (Real.cos α / Real.sin α : ℝ) * ∑ i, x i ^ 2 := by
    calc
      _ = isotropicFirstBlowupDenominator α x (0, 2 * (Real.sin α : ℂ) * Complex.I) := by
        rw [isotropicFirstBlowupDenominator_center hα hπ]
        ring
      _ = _ := by simpa only [mul_one] using isotropicFirstBlowupDenominator_radial_center hα hπ x 1
  rw [hd]

theorem isotropic_first_actual_scaled_jet_limit {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℝ) (hx : ∑ i, x i = 0) (j : ℕ) :
    Tendsto (fun s : ℂ => (s ^ (2 * j + 2) / s ^ (2 * N.choose 2)) *
      iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
        (h, fun i => s * (x i : ℂ))) (s ^ 2 * isotropicRadialIncrement α (s ^ 2)))
      (𝓝[≠] (0 : ℂ))
      (𝓝 ((edgeVandermondeSquared (fun i => (x i : ℂ)) * isotropicFirstCenterAmplitude N α) *
        ((-1 : ℂ) ^ j * (j.factorial : ℂ) *
          (-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) ^ j /
          (2 * (N : ℂ) - Complex.I * (Real.cos α / Real.sin α : ℝ) *
            ∑ i, (x i : ℂ) ^ 2) ^ (j + 1)))) := by
  let X : Fin N → ℂ := fun i => (x i : ℂ)
  let t0 : ℂ := 2 * (Real.sin α : ℂ) * Complex.I
  have hX : ∑ i, X i = 0 := by
    simp only [X, ← Complex.ofReal_sum, hx, Complex.ofReal_zero]
  have ha := isotropicFirstScaledDensity_analytic hα hπ σ X t0
    (isotropicFirstBlowupDenominator_radial_ne_zero hN hα hπ x)
  have hsq : AnalyticAt ℂ (fun s : ℂ => s ^ 2) 0 := analyticAt_id.pow 2
  have hmap : ContinuousAt (fun s : ℂ => isotropicRadialIncrement α (s ^ 2)) 0 :=
    ((isotropicRadialIncrement_analytic α).comp_of_eq hsq (by norm_num)).continuousAt
  have hcenter : isotropicRadialIncrement α ((0 : ℂ) ^ 2) = t0 := by
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), isotropicRadialIncrement_center]
  have hc : Tendsto (fun s : ℂ => iteratedDeriv j
      (fun v => isotropicFirstScaledDensity α σ X (s, v)) (isotropicRadialIncrement α (s ^ 2)))
      (𝓝 (0 : ℂ)) (𝓝 (iteratedDeriv j
        (fun v => isotropicFirstScaledDensity α σ X (0, v)) t0)) :=
    by simpa only [hcenter] using
      (second_parameter_variable_jet_continuous ha hmap hcenter j).tendsto
  have hc' := hc.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  rw [isotropicFirstScaledDensity_radial_jet_center hα hπ σ hres] at hc'
  apply hc'.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (isotropicFirstScaledDensity_jet_quotient hα hπ σ hres X hX s
    (isotropicRadialIncrement α (s ^ 2)) hs j).symm

end
end IsingBulk.AnisoF002.Isotropic
