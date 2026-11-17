import IsingBulk.AnisoF002.C03.IsotropicFirstAmplitude
import IsingBulk.AnisoF002.C03.IsotropicFirstRadialFill
import IsingBulk.AnisoF002.C03.RegularCollisionJetLimit

/-!
# Exact blow-up and parameter jets of the full isotropic first density

This keeps the original signed product kernel, every pair, factorial, and
independent-coordinate normalization. The scaling identity holds for the
literal physical density. Its jointly analytic filling supplies the true
pointwise derivative limit along the original exterior radial approach.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstJointDensity {N : ℕ} (α : ℝ) (σ : ℂ)
    (p : ℂ × (Fin N → ℂ)) : ℂ :=
  isotropicBarePhysicalDensity ((2 * Real.cos α : ℂ) + p.1) σ
    (fun i => -(α : ℂ) + p.2 i)

def isotropicFirstScaledDensity {N : ℕ} (α : ℝ) (σ : ℂ) (x : Fin N → ℂ)
    (p : ℂ × ℂ) : ℂ :=
  edgeVandermondeSquared x *
    isotropicFirstAmplitude α σ (p.1 ^ 2 * p.2, fun i => p.1 * x i) /
      isotropicFirstBlowupDenominator α x p

theorem isotropicFirstScaledDensity_exact {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (hx : ∑ i, x i = 0) (s t : ℂ) (hs : s ≠ 0) :
    s ^ 2 * isotropicFirstJointDensity α σ (s ^ 2 * t, fun i => s * x i) =
      s ^ (2 * N.choose 2) * isotropicFirstScaledDensity α σ x (s, t) := by
  rw [isotropicFirstJointDensity, isotropicFirstDensity_exact,
    edgeVandermondeSquared_scaling, isotropicFirstDenominator_blowup hα hπ σ hres x hx]
  unfold isotropicFirstScaledDensity
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp

theorem isotropicFirstScaledDensity_analytic {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) (x : Fin N → ℂ) (t : ℂ)
    (hq : isotropicFirstBlowupDenominator α x (0, t) ≠ 0) :
    AnalyticAt ℂ (isotropicFirstScaledDensity α σ x) (0, t) := by
  have hm : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (p.1 ^ 2 * p.2, fun i => p.1 * x i)) (0, t) :=
    ((analyticAt_fst.pow 2).mul analyticAt_snd).prod
      (AnalyticAt.pi fun _ => analyticAt_fst.mul analyticAt_const)
  have ha := (isotropicFirstAmplitude_analyticAt (N := N) hα hπ σ).comp_of_eq hm
    (by simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, Pi.zero_def])
  exact (analyticAt_const.mul ha).div (isotropicFirstBlowupDenominator_analytic hα hπ x t) hq

theorem isotropicFirstScaledDensity_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (t : ℂ) :
    isotropicFirstScaledDensity α σ x (0, t) =
      edgeVandermondeSquared x * isotropicFirstCenterAmplitude N α /
        ((-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) * t +
          (-Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) * ∑ i, x i ^ 2)) := by
  simp only [isotropicFirstScaledDensity, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, ← Pi.zero_def, isotropicFirstAmplitude_center hα hπ σ hres,
    isotropicFirstBlowupDenominator_center hα hπ]
  congr 1
  ring

theorem isotropicFirstScaledDensity_jet_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (j : ℕ) (t : ℂ) :
    iteratedDeriv j (fun v => isotropicFirstScaledDensity α σ x (0, v)) t =
      (edgeVandermondeSquared x * isotropicFirstCenterAmplitude N α) *
        ((-1 : ℂ) ^ j * (j.factorial : ℂ) *
          (-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) ^ j /
          ((-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) * t +
            (-Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) * ∑ i, x i ^ 2)) ^ (j + 1)) := by
  have he : (fun v => isotropicFirstScaledDensity α σ x (0, v)) =
      fun v => (edgeVandermondeSquared x * isotropicFirstCenterAmplitude N α) *
        (((-Complex.I / (Real.sin α : ℂ) * (N : ℂ)) * v +
          (-Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) * ∑ i, x i ^ 2))⁻¹) := by
    funext v
    rw [isotropicFirstScaledDensity_center hα hπ σ hres, div_eq_mul_inv]
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_affine_reciprocal]

theorem isotropicFirstScaledDensity_jet_exact {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (hx : ∑ i, x i = 0) (s t : ℂ) (hs : s ≠ 0) (j : ℕ) :
    s ^ (2 * j + 2) *
      iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
        (h, fun i => s * x i)) (s ^ 2 * t) =
      s ^ (2 * N.choose 2) *
        iteratedDeriv j (fun v => isotropicFirstScaledDensity α σ x (s, v)) t := by
  have he : (fun v => s ^ 2 * isotropicFirstJointDensity α σ
      (s ^ 2 * v, fun i => s * x i)) =
      fun v => s ^ (2 * N.choose 2) * isotropicFirstScaledDensity α σ x (s, v) := by
    funext v
    exact isotropicFirstScaledDensity_exact hα hπ σ hres x hx s v hs
  have hj := congrArg (fun f : ℂ → ℂ => iteratedDeriv j f t) he
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_mul_unconditional j
      (fun h => isotropicFirstJointDensity α σ (h, fun i => s * x i)) (s ^ 2) t,
    ← pow_mul, ← mul_assoc, ← pow_add] at hj
  convert hj using 1
  congr 2
  omega

theorem isotropicFirstScaledDensity_jet_quotient {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (hx : ∑ i, x i = 0) (s t : ℂ) (hs : s ≠ 0) (j : ℕ) :
    (s ^ (2 * j + 2) / s ^ (2 * N.choose 2)) *
      iteratedDeriv j (fun h => isotropicFirstJointDensity α σ
        (h, fun i => s * x i)) (s ^ 2 * t) =
      iteratedDeriv j (fun v => isotropicFirstScaledDensity α σ x (s, v)) t := by
  apply (mul_left_cancel₀ (pow_ne_zero (2 * N.choose 2) hs))
  have he := isotropicFirstScaledDensity_jet_exact hα hπ σ hres x hx s t hs j
  field_simp [hs]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using he

end
end IsingBulk.AnisoF002.Isotropic
