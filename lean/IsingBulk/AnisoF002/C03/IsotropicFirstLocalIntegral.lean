import IsingBulk.AnisoF002.C03.IsotropicFirstScaledBounds
import IsingBulk.AnisoF002.C03.IsotropicJointPhysicalAnalytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual first-chart dominated integral limit

The cutoff is a fixed quadratic real shape ball in the literal independent
coordinates. Its scaled domain expands to all of R^(N-1). The original
physical density jets, with the whole Vandermonde, converge under that
Lebesgue integral. No prescribed analytic remainder is assumed.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem isotropic_flatConstrainedAngles_sum (n : ℕ) (q : Fin n → ℝ) :
    ∑ i, flatConstrainedAngles q i = 0 := by
  simp [flatConstrainedAngles, Fin.sum_univ_castSucc]

theorem isotropicRadialParameter_im_pos {α e : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (he : 0 < e) :
    0 < (isotropicRadialParameter α e).im := by
  rw [isotropicRadialParameter_im_shift α e (by linarith)]
  exact div_pos (mul_pos (mul_pos (Real.sin_pos_of_pos_of_lt_pi hα hπ) he)
    (by linarith)) (by linarith)

theorem isotropicFirstRealScaledJet_continuous {N : ℕ} (hN : 0 < N) {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (j : ℕ) {s : ℝ} (hs : 0 < s) :
    Continuous (isotropicFirstRealScaledJet (N := N) α σ j s) := by
  have hS := isotropicRadialParameter_im_pos hα hπ (sq_pos_of_pos hs)
  have hc := isotropic_physical_temperature_jets_continuous hN σ hσ hS j
  have hm : Continuous (fun x : Fin N → ℝ => fun i => -α + s * x i) := by fun_prop
  have he (x : Fin N → ℝ) : isotropicFirstRealScaledJet α σ j s x =
      ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * N.choose 2)) *
        iteratedDeriv j (fun T => isotropicBarePhysicalDensity T σ
          (fun i => ((-α + s * x i : ℝ) : ℂ))) (isotropicRadialParameter α (s ^ 2)) := by
    have hf : (fun h => isotropicFirstJointDensity α σ (h, fun i => ((s * x i : ℝ) : ℂ))) =
        fun h => isotropicBarePhysicalDensity ((2 * Real.cos α : ℂ) + h) σ
          (fun i => ((-α + s * x i : ℝ) : ℂ)) := by
      funext h
      unfold isotropicFirstJointDensity
      congr 1
      funext i
      push_cast
      rfl
    unfold isotropicFirstRealScaledJet
    rw [hf]
    congr 1
    have hh := congrFun (iteratedDeriv_comp_const_add (n := j)
      (f := fun T => isotropicBarePhysicalDensity T σ (fun i => ((-α + s * x i : ℝ) : ℂ)))
      (s := (2 * Real.cos α : ℂ)))
      (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ))
    rw [show (2 * Real.cos α : ℂ) +
      (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)) =
        isotropicRadialParameter α (s ^ 2) by ring] at hh
    exact hh
  rw [show isotropicFirstRealScaledJet (N := N) α σ j s = _ from funext he]
  exact continuous_const.mul (hc.comp hm)

def isotropicFirstScaledLocal {n : ℕ} (α : ℝ) (σ : ℂ) (j : ℕ) (ρ s : ℝ)
    (q : Fin n → ℝ) : ℂ :=
  if angularQuadratic (flatConstrainedAngles (s • q)) < ρ then
    isotropicFirstRealScaledJet α σ j s (flatConstrainedAngles q) else 0

theorem isotropicFirstScaledLocal_limit {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    {ρ : ℝ} (hρ : 0 < ρ) (q : Fin n → ℝ) (j : ℕ) :
    Tendsto (fun s : ℝ => isotropicFirstScaledLocal α σ j ρ s q) (𝓝[>] (0 : ℝ))
      (𝓝 (isotropicFirstLeadingJet α j (flatConstrainedAngles q))) := by
  have hc : ContinuousAt (fun s : ℝ => angularQuadratic (flatConstrainedAngles (s • q))) 0 :=
    ((angularQuadratic_continuous _).comp
      ((flatConstrainedAngles_continuous n).comp (by fun_prop))).continuousAt
  have hzero : angularQuadratic (flatConstrainedAngles ((0 : ℝ) • q)) = 0 := by
    have hf : flatConstrainedAngles ((0 : ℝ) • q) = fun i => 0 * flatConstrainedAngles q i :=
      flatConstrainedAngles_mul q 0
    rw [hf]
    simp [angularQuadratic]
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, angularQuadratic (flatConstrainedAngles (s • q)) < ρ :=
    hc.eventually (Iio_mem_nhds (by
      change angularQuadratic (flatConstrainedAngles ((0 : ℝ) • q)) < ρ
      rw [hzero]
      exact hρ))
  apply (isotropicFirstRealScaledJet_limit (Nat.succ_pos n) hα hπ σ hres
    (flatConstrainedAngles q) (isotropic_flatConstrainedAngles_sum n q) j).congr'
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds] with s hs
  simp only [isotropicFirstScaledLocal, ite_eq_left hs]

theorem isotropicFirstScaledLocal_measurable {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (j : ℕ) (ρ : ℝ) {s : ℝ} (hs : 0 < s) :
    Measurable (isotropicFirstScaledLocal (n := n) α σ j ρ s) := by
  have hc : Continuous (fun q : Fin n → ℝ => angularQuadratic (flatConstrainedAngles (s • q))) :=
    (angularQuadratic_continuous _).comp ((flatConstrainedAngles_continuous n).comp (by fun_prop))
  apply Measurable.ite (isOpen_lt hc continuous_const).measurableSet
  · exact ((isotropicFirstRealScaledJet_continuous (Nat.succ_pos n) hα hπ σ hσ j hs).comp
      (flatConstrainedAngles_continuous n)).measurable
  · exact measurable_const

theorem exists_isotropic_first_local_integral_limit {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (j : ℕ) (hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun s : ℝ => ∫ q : Fin n → ℝ, isotropicFirstScaledLocal α σ j ρ s q)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ q : Fin n → ℝ, isotropicFirstLeadingJet α j (flatConstrainedAngles q))) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := exists_isotropic_first_scaled_jet_majorant
    (Nat.succ_pos n) hα hhalf σ hres j
  let ρ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  refine ⟨ρ, hρ, ?_⟩
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ^ 2 < ρ :=
    ((show ContinuousAt (fun s : ℝ => s ^ 2) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa using hρ))).filter_mono nhdsWithin_le_nhds
  apply tendsto_integral_filter_of_dominated_convergence
    (fun q => C * collisionRationalMajorant n (j + 1) q)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (isotropicFirstScaledLocal_measurable hα hπ σ hσ j ρ hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hsmall] with s hs he
    exact Filter.Eventually.of_forall fun q => by
      by_cases hq : angularQuadratic (flatConstrainedAngles (s • q)) < ρ
      · rw [isotropicFirstScaledLocal, ite_eq_left hq]
        have hflat : flatConstrainedAngles (s • q) = fun i => s * flatConstrainedAngles q i :=
          flatConstrainedAngles_mul q s
        have hsq : s ^ 2 + angularQuadratic (fun i => s * flatConstrainedAngles q i) < δ := by
          rw [hflat] at hq
          dsimp only [ρ] at he hq
          linarith
        simpa only [collisionRationalMajorant, mul_div_assoc] using
          hb s hs (flatConstrainedAngles q) (isotropic_flatConstrainedAngles_sum n q) hsq
      · rw [isotropicFirstScaledLocal, ite_eq_right hq, norm_zero]
        exact mul_nonneg hC.le (collisionRationalMajorant_nonneg _ _ _)
  · exact (collisionRationalMajorant_integrable hbudget).const_mul C
  · exact Filter.Eventually.of_forall fun q => isotropicFirstScaledLocal_limit hα hπ σ hres hρ q j

end
end IsingBulk.AnisoF002.Isotropic
