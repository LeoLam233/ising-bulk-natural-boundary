import IsingBulk.AnisoF002.C03.IsotropicFirstDenominator
import IsingBulk.AnisoF002.C03.RegularCollisionKernel

/-!
# The literal isotropic first-chart amplitude through all collisions

The factorial and independent-coordinate Haar normalization, all one-body
factors, every pair, and the signed product numerator are retained. The
entire sinc fills every collision simultaneously. No Vandermonde division
is used. The center is the actual physical amplitude and is nonzero.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicFirstAmplitude {N : ℕ} (α : ℝ) (σ : ℂ)
    (p : ℂ × (Fin N → ℂ)) : ℂ :=
  isotropicParticleNormalization N *
    (1 + σ * Complex.exp (-(∑ i, isotropicFirstLogPhase α (p.1, p.2 i)))) *
    (∏ i, (Complex.sinh (isotropicFirstLogPhase α (p.1, p.2 i)))⁻¹) *
    ∏ ij ∈ indexPairs N,
      (complexSinc ((p.2 ij.1 - p.2 ij.2) / 2) / 2) ^ 2 /
        Complex.sinh ((isotropicFirstLogPhase α (p.1, p.2 ij.1) +
          isotropicFirstLogPhase α (p.1, p.2 ij.2)) / 2) ^ 2

def isotropicFirstCenterAmplitude (N : ℕ) (α : ℝ) : ℂ :=
  isotropicParticleNormalization N * 2 * (((Real.sin α : ℂ) * Complex.I)⁻¹) ^ N *
    (1 / (4 * ((Real.sin α : ℂ) * Complex.I) ^ 2)) ^ (N.choose 2)

theorem isotropicFirst_pair_exact (α : ℝ) (h x y : ℂ) :
    canceledPair 1 (upperEdgeRoot (isotropicFirstDispersion α (h, x)))
      (upperEdgeRoot (isotropicFirstDispersion α (h, y)))
      (Complex.exp ((-(α : ℂ) + x) * Complex.I))
      (Complex.exp ((-(α : ℂ) + y) * Complex.I)) =
      (x - y) ^ 2 * ((complexSinc ((x - y) / 2) / 2) ^ 2 /
        Complex.sinh ((isotropicFirstLogPhase α (h, x) +
          isotropicFirstLogPhase α (h, y)) / 2) ^ 2) := by
  rw [canceledPair_eq_sinePair, ← upperEdgePhase_exp_neg, ← upperEdgePhase_exp_neg,
    sinePairCoefficient_exp]
  rw [show (-(α : ℂ) + x) - (-(α : ℂ) + y) = x - y by ring,
    sine_squared_collision_factorization]
  unfold isotropicFirstLogPhase
  ring

theorem isotropicFirstDensity_exact {N : ℕ} (α : ℝ) (σ h : ℂ) (x : Fin N → ℂ) :
    isotropicBarePhysicalDensity ((2 * Real.cos α : ℂ) + h) σ
      (fun i => -(α : ℂ) + x i) =
      edgeVandermondeSquared x * isotropicFirstAmplitude α σ (h, x) /
        isotropicFirstDenominator α σ (h, x) := by
  have hroot : (∏ i, isotropicInteriorRoot
      ((2 * Real.cos α : ℂ) + h, -(α : ℂ) + x i)) =
      Complex.exp (-(∑ i, isotropicFirstLogPhase α (h, x i))) := by
    simp only [isotropicInteriorRoot, isotropicDispersion, isotropicFirstLogPhase,
      isotropicFirstDispersion, ← upperEdgePhase_exp_neg, ← Complex.exp_sum,
      Finset.sum_neg_distrib]
  unfold isotropicBarePhysicalDensity
  rw [hroot]
  have hb (i : Fin N) : Complex.I * upperPhysicalPhase
      (isotropicDispersion ((2 * Real.cos α : ℂ) + h, -(α : ℂ) + x i)) =
      isotropicFirstLogPhase α (h, x i) := I_mul_upperPhysicalPhase _
  simp_rw [hb]
  have hp (ij : Fin N × Fin N) := isotropicFirst_pair_exact α h (x ij.1) (x ij.2)
  change isotropicParticleNormalization N *
      ((1 + σ * Complex.exp (-(∑ i, isotropicFirstLogPhase α (h, x i)))) /
        (1 - σ * Complex.exp (-(∑ i, isotropicFirstLogPhase α (h, x i))))) *
      (∏ i, (Complex.sinh (isotropicFirstLogPhase α (h, x i)))⁻¹) *
      (∏ ij ∈ indexPairs N, canceledPair 1
        (upperEdgeRoot (isotropicFirstDispersion α (h, x ij.1)))
        (upperEdgeRoot (isotropicFirstDispersion α (h, x ij.2)))
        (Complex.exp ((-(α : ℂ) + x ij.1) * Complex.I))
        (Complex.exp ((-(α : ℂ) + x ij.2) * Complex.I))) = _
  simp_rw [hp]
  rw [Finset.prod_mul_distrib, isotropicFirstDenominator_exp]
  unfold edgeVandermondeSquared isotropicFirstAmplitude
  ring

theorem isotropicFirstAmplitude_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1) :
    isotropicFirstAmplitude α σ ((0 : ℂ), (0 : Fin N → ℂ)) =
      isotropicFirstCenterAmplitude N α := by
  have hp : ((α : ℂ) * Complex.I + (α : ℂ) * Complex.I) / 2 = (α : ℂ) * Complex.I := by ring
  simp only [isotropicFirstAmplitude, Pi.zero_apply, isotropicFirstLogPhase_center hα hπ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hres,
    hp, Complex.sinh_mul_I, ← Complex.ofReal_sin, sub_self, zero_div, complexSinc_zero,
    Finset.prod_const, card_indexPairs, isotropicFirstCenterAmplitude]
  congr 1
  · ring
  · congr 1
    ring

theorem isotropicFirstCenterAmplitude_ne_zero {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) : isotropicFirstCenterAmplitude N α ≠ 0 := by
  have hs : (Real.sin α : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπ).ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : isotropicParticleNormalization N ≠ 0 := by
    unfold isotropicParticleNormalization
    exact inv_ne_zero (mul_ne_zero (by exact_mod_cast N.factorial_ne_zero)
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hπc)))
  unfold isotropicFirstCenterAmplitude
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn (by norm_num))
    (pow_ne_zero _ (inv_ne_zero (mul_ne_zero hs Complex.I_ne_zero))))
      (pow_ne_zero _ (one_div_ne_zero (mul_ne_zero (by norm_num)
        (pow_ne_zero _ (mul_ne_zero hs Complex.I_ne_zero)))))

theorem isotropicFirstAmplitude_analyticAt {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) :
    AnalyticAt ℂ (isotropicFirstAmplitude (N := N) α σ) (0, 0) := by
  have hv (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => p.2 i) (0, 0) := by
    have hproj : AnalyticAt ℂ (fun x : Fin N → ℂ => x i) (0 : Fin N → ℂ) :=
      (show (Fin N → ℂ) →L[ℂ] ℂ from ContinuousLinearMap.proj i).analyticAt _
    exact hproj.comp_of_eq (f := fun p : ℂ × (Fin N → ℂ) => p.2) analyticAt_snd rfl
  have hγ (i : Fin N) : AnalyticAt ℂ
      (fun p : ℂ × (Fin N → ℂ) => isotropicFirstLogPhase α (p.1, p.2 i)) (0, 0) :=
    (isotropicFirstLogPhase_analyticAt hα hπ).comp_of_eq
      (f := fun p : ℂ × (Fin N → ℂ) => (p.1, p.2 i)) (analyticAt_fst.prod (hv i)) rfl
  have hs : (Real.sin α : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπ).ne'
  have hbody (i : Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      (Complex.sinh (isotropicFirstLogPhase α (p.1, p.2 i)))⁻¹) (0, 0) := by
    apply (Complex.analyticAt_sinh.comp (hγ i)).inv
    change Complex.sinh (isotropicFirstLogPhase α (0, 0)) ≠ 0
    simpa only [isotropicFirstLogPhase_center hα hπ,
      Complex.sinh_mul_I, ← Complex.ofReal_sin] using mul_ne_zero hs Complex.I_ne_zero
  have hpair (ij : Fin N × Fin N) : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
      (complexSinc ((p.2 ij.1 - p.2 ij.2) / 2) / 2) ^ 2 /
        Complex.sinh ((isotropicFirstLogPhase α (p.1, p.2 ij.1) +
          isotropicFirstLogPhase α (p.1, p.2 ij.2)) / 2) ^ 2) (0, 0) := by
    apply ((((complexSinc_analyticAt _).comp (((hv ij.1).sub (hv ij.2)).div_const)).div_const).pow 2).div
      ((Complex.analyticAt_sinh.comp (((hγ ij.1).add (hγ ij.2)).div_const)).pow 2)
    have he : ((α : ℂ) * Complex.I + (α : ℂ) * Complex.I) / 2 = (α : ℂ) * Complex.I := by ring
    change Complex.sinh ((isotropicFirstLogPhase α (0, 0) +
      isotropicFirstLogPhase α (0, 0)) / 2) ^ 2 ≠ 0
    simpa only [isotropicFirstLogPhase_center hα hπ, he,
      Complex.sinh_mul_I, ← Complex.ofReal_sin] using pow_ne_zero 2 (mul_ne_zero hs Complex.I_ne_zero)
  exact ((analyticAt_const.mul (analyticAt_const.add
    (analyticAt_const.mul ((Finset.univ.analyticAt_fun_sum fun i _ => hγ i).neg.cexp)))).mul
      (Finset.univ.analyticAt_fun_prod fun i _ => hbody i)).mul
        ((indexPairs N).analyticAt_fun_prod fun ij _ => hpair ij)

end
end IsingBulk.AnisoF002.Isotropic
