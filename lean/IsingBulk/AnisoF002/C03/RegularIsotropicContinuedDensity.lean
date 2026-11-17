import IsingBulk.AnisoF002.C03.RegularIsotropicProtectedRoots
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy

/-!
# The protected density is the original physical germ

The one-body factors are rewritten exactly in their actual reciprocal
roots. The prescribed continuation agrees with the interior physical
branch near the center, so all ordinary parameter jets are those of the
original complete normalized density.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

def mixedContinuedDensity {N : ℕ} (S σ : ℂ) (η τ : ℝ) (θ : Fin N → ℝ) (z : ℂ) : ℂ :=
  isotropicParticleNormalization N *
    ((1 + σ * ∏ i, mixedContinuedRoots S η τ θ z i) /
      (1 - σ * ∏ i, mixedContinuedRoots S η τ θ z i)) *
    (∏ i, 2 * mixedContinuedRoots S η τ θ z i /
      (1 - mixedContinuedRoots S η τ θ z i ^ 2)) *
    ∏ ij ∈ indexPairs N, canceledPair 1
      (mixedContinuedRoots S η τ θ z ij.1) (mixedContinuedRoots S η τ θ z ij.2)
      (Complex.exp (actualHomotopyAngle η τ 1 θ ij.1 * Complex.I))
      (Complex.exp (actualHomotopyAngle η τ 1 θ ij.2 * Complex.I))

theorem isotropic_oneBody_eq (S w : ℂ) :
    2 * isotropicInteriorRoot (S, w) / (1 - isotropicInteriorRoot (S, w) ^ 2) =
      (Complex.sinh (Complex.I * upperPhysicalPhase (isotropicDispersion (S, w))))⁻¹ := by
  have hh := oneBody_exp_eq_inv_sinh (upperPhysicalPhase (isotropicDispersion (S, w)) * Complex.I)
  rw [upperPhysicalPhase_exp] at hh
  simpa only [isotropicInteriorRoot, one_div, mul_comm Complex.I] using hh

theorem isotropicBarePhysicalDensity_root_formula {N : ℕ} (S σ : ℂ) (w : Fin N → ℂ) :
    isotropicBarePhysicalDensity S σ w =
      isotropicParticleNormalization N *
        ((1 + σ * ∏ i, isotropicInteriorRoot (S, w i)) /
          (1 - σ * ∏ i, isotropicInteriorRoot (S, w i))) *
        (∏ i, 2 * isotropicInteriorRoot (S, w i) / (1 - isotropicInteriorRoot (S, w i) ^ 2)) *
        ∏ ij ∈ indexPairs N, canceledPair 1
          (isotropicInteriorRoot (S, w ij.1)) (isotropicInteriorRoot (S, w ij.2))
          (Complex.exp (w ij.1 * Complex.I)) (Complex.exp (w ij.2 * Complex.I)) := by
  simp only [isotropicBarePhysicalDensity, isotropic_oneBody_eq]

theorem mixedContinuedRoots_center {N : ℕ} (S : ℂ) (η τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    mixedContinuedRoots S η τ θ 0 i = isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i) := by
  simp only [mixedContinuedRoots, continuedRoots, add_zero, reciprocalRootContinuation_center]

theorem mixedContinuedRoots_eventually_physical {N : ℕ} (S : ℂ) (hS : 0 < S.im)
    (η τ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, ∀ i, mixedContinuedRoots S η τ θ z i =
      isotropicInteriorRoot (S + z, actualHomotopyAngle η τ 1 θ i) := by
  apply Filter.eventually_all.mpr
  intro i
  let w := actualHomotopyAngle η τ 1 θ i
  let W := isotropicDispersion (S, w)
  let r := isotropicInteriorRoot (S, w)
  have hWi : 0 < W.im := actual_balanced_homotopy_sheet S hS η τ 1 hη hτ zero_le_one θ i
  have hp : r ^ 2 - 2 * W * r + 1 = 0 := isotropicInteriorRoot_polynomial (S, w)
  have hd : W - r ≠ 0 := reciprocalRootContinuation_simple hp
    (upperEdgeRoot_pair_denominator (Or.inl hWi) (Or.inl hWi))
  have ha : AnalyticAt ℂ (fun z => mixedContinuedRoots S η τ θ z i) 0 := by
    have ho : AnalyticAt ℂ (reciprocalRootContinuation W r) (W + (0 : ℂ)) := by
      simpa only [add_zero] using reciprocalRootContinuation_analyticAt W r
    exact ho.comp (f := fun z : ℂ => W + z) (analyticAt_const.add analyticAt_id)
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖mixedContinuedRoots S η τ θ z i‖ < 1 := by
    have hr0 : ‖mixedContinuedRoots S η τ θ 0 i‖ < 1 := by
      rw [mixedContinuedRoots_center]
      exact upperEdgeRoot_norm_lt_one hWi
    exact ha.continuousAt.norm.eventually (Iio_mem_nhds hr0)
  have hi : ∀ᶠ z : ℂ in 𝓝 0,
      0 < (isotropicDispersion (S + z, w)).im := by
    have hc : ContinuousAt (fun z : ℂ => (isotropicDispersion (S + z, w)).im) 0 := by
      unfold isotropicDispersion
      fun_prop
    have h0 : 0 < (isotropicDispersion (S + (0 : ℂ), w)).im := by
      simpa only [add_zero] using hWi
    exact hc.eventually (Ioi_mem_nhds h0)
  filter_upwards [hn, hi] with z hz hzi
  apply isotropicInteriorRoot_unique (S + z, w) hzi _ _ hz
  have he := reciprocalRootContinuation_polynomial hp hd (W + z)
  convert he using 1
  dsimp [W, w, mixedContinuedRoots, continuedRoots, isotropicDispersion]
  ring

theorem mixedContinuedDensity_eventually_physical {N : ℕ} (S σ : ℂ) (hS : 0 < S.im)
    (η τ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) :
    (fun z => mixedContinuedDensity S σ η τ θ z) =ᶠ[𝓝 0]
      (fun z => isotropicBarePhysicalDensity (S + z) σ (actualHomotopyAngle η τ 1 θ)) := by
  filter_upwards [mixedContinuedRoots_eventually_physical S hS η τ hη hτ θ] with z hz
  rw [isotropicBarePhysicalDensity_root_formula]
  simp only [mixedContinuedDensity, hz]

theorem mixedContinuedDensity_physical_jets {N : ℕ} (S σ : ℂ) (hS : 0 < S.im)
    (η τ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (j : ℕ) :
    iteratedDeriv j (mixedContinuedDensity S σ η τ θ) 0 =
      iteratedDeriv j (fun z => isotropicBarePhysicalDensity (S + z) σ (actualHomotopyAngle η τ 1 θ)) 0 :=
  (mixedContinuedDensity_eventually_physical S σ hS η τ hη hτ θ).iteratedDeriv_eq j

end
end IsingBulk.AnisoF002.Isotropic
