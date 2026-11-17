import IsingBulk.AnisoF002.C03.NegativeAngularExponentialMoment

/-!
# Uniform averaged exponential perturbation on the actual angular law

The complete angular exponential moment yields the O(sqrt epsilon)
central-region comparison used in frozen Proposition 4.3.  This bound
integrates over the whole constrained angular measure.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set

theorem real_exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero x)] at h
  nlinarith

theorem exponential_perturbation_majorant {δ z : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32) (hz : 0 ≤ z) :
    Real.exp (δ * (1 + z)) - 1 ≤ δ * Real.exp (1 / 32) * momentProfile z := by
  calc
    _ ≤ (δ * (1 + z)) * Real.exp (δ * (1 + z)) := real_exp_sub_one_le_mul_exp _
    _ ≤ (δ * (1 + z)) * Real.exp (1 / 32 + z / 32) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      nlinarith
    _ = _ := by rw [Real.exp_add]; unfold momentProfile; ring

def angularPerturbationConstant : ℝ := Real.exp (1 / 32) * angularMomentConstant

theorem angularPerturbationConstant_pos : 0 < angularPerturbationConstant :=
  mul_pos (Real.exp_pos _) angularMomentConstant_pos

theorem uniform_angular_exponential_perturbation {d : ℕ} (hd : 2 ≤ d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32) :
    (∫ θ : AngularSphere d, (Real.exp (δ * (1 + angularZ θ)) - 1) ∂angularLaw d) ≤
      angularPerturbationConstant * δ := by
  have hd0 : 0 < d := by omega
  have := angularLaw_isProbability hd0
  have hf : Continuous (fun θ : AngularSphere d => Real.exp (δ * (1 + angularZ θ)) - 1) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.add (continuous_angularZ d)))).sub
      continuous_const
  have hi : Integrable (fun θ : AngularSphere d => Real.exp (δ * (1 + angularZ θ)) - 1)
      (angularLaw d) := hf.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hm := (angular_moment_integrable hd0).const_mul (δ * Real.exp (1 / 32))
  have h := integral_mono hi hm
    (fun θ => exponential_perturbation_majorant hδ hδsmall (angularZ_nonneg θ))
  rw [integral_const_mul] at h
  have hb := uniform_angular_exponential_moment hd
  change (∫ θ : AngularSphere d, momentProfile (angularZ θ) ∂angularLaw d) ≤
    angularMomentConstant at hb
  calc
    _ ≤ (δ * Real.exp (1 / 32)) *
        (∫ θ : AngularSphere d, momentProfile (angularZ θ) ∂angularLaw d) := h
    _ ≤ (δ * Real.exp (1 / 32)) * angularMomentConstant :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by unfold angularPerturbationConstant; ring

theorem uniform_angular_dominated_perturbation {d : ℕ} (hd : 2 ≤ d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    {E : AngularSphere d → ℝ} (hE : AEStronglyMeasurable E (angularLaw d))
    (hE0 : ∀ θ, 0 ≤ E θ) (hbound : ∀ θ, E θ ≤ δ * (1 + angularZ θ)) :
    Integrable (fun θ => Real.exp (E θ) - 1) (angularLaw d) ∧
      (∫ θ, (Real.exp (E θ) - 1) ∂angularLaw d) ≤ angularPerturbationConstant * δ := by
  have hd0 : 0 < d := by omega
  have := angularLaw_isProbability hd0
  have hf : Continuous (fun θ : AngularSphere d => Real.exp (δ * (1 + angularZ θ)) - 1) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.add (continuous_angularZ d)))).sub
      continuous_const
  have hi : Integrable (fun θ : AngularSphere d => Real.exp (δ * (1 + angularZ θ)) - 1)
      (angularLaw d) := hf.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have he : ∀ θ, 0 ≤ Real.exp (E θ) - 1 := by
    intro θ
    exact sub_nonneg.mpr (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (hE0 θ))
  have hle : ∀ θ, Real.exp (E θ) - 1 ≤ Real.exp (δ * (1 + angularZ θ)) - 1 :=
    fun θ => sub_le_sub_right (Real.exp_le_exp.mpr (hbound θ)) 1
  have hEi : Integrable (fun θ => Real.exp (E θ) - 1) (angularLaw d) := by
    apply hi.mono' ((Real.continuous_exp.comp_aestronglyMeasurable hE).sub aestronglyMeasurable_const)
    apply Filter.Eventually.of_forall
    intro θ
    change ‖Real.exp (E θ) - 1‖ ≤ Real.exp (δ * (1 + angularZ θ)) - 1
    rw [Real.norm_of_nonneg (he θ)]
    exact hle θ
  exact ⟨hEi, (integral_mono hEi hi hle).trans (uniform_angular_exponential_perturbation hd hδ hδsmall)⟩

end
end IsingBulk.AnisoF002.NegativeHT.Angular
