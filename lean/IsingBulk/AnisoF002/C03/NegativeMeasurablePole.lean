import IsingBulk.AnisoF002.C03.NegativePoleExtraction
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Measurability of a filled pole with a moving angular center

Derivatives at a measurable moving center are limits of genuine measurable
difference quotients.  This supplies the diagonal value of each divided
difference; no measurability of a nonconstructively chosen derivative is
assumed.  The result applies twice to the exact physical pole remainder.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {X : Type*} [MeasurableSpace X]

theorem measurable_deriv_at_moving_center {F : ℂ → X → ℂ} {P : X → ℂ}
    (hF : Measurable (Function.uncurry F)) (hP : Measurable P)
    (hd : ∀ x, DifferentiableAt ℂ (fun t => F t x) (P x)) :
    Measurable (fun x => deriv (fun t => F t x) (P x)) := by
  let u : ℕ → ℂ := fun m => 1 / ((m : ℂ) + 1)
  have hu0 (m : ℕ) : u m ≠ 0 := by
    dsimp [u]
    apply one_div_ne_zero
    exact_mod_cast (by positivity : (m : ℝ) + 1 ≠ 0)
  have hu : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hu0⟩
  let Q : ℕ → X → ℂ := fun m x =>
    (u m)⁻¹ * (F (P x + u m) x - F (P x) x)
  apply measurable_of_tendsto_metrizable (f := Q)
  · intro m
    exact measurable_const.mul
      ((hF.comp ((hP.add_const (u m)).prodMk measurable_id)).sub
        (hF.comp (hP.prodMk measurable_id)))
  · apply tendsto_pi_nhds.mpr
    intro x
    simpa only [Q, smul_eq_mul, Function.comp_def] using
      (hd x).hasDerivAt.tendsto_slope_zero.comp hu

theorem measurable_dslope_moving_center {F : ℂ → X → ℂ} {P : X → ℂ}
    (hF : Measurable (Function.uncurry F)) (hP : Measurable P)
    (hd : ∀ x, DifferentiableAt ℂ (fun t => F t x) (P x)) :
    Measurable (fun p : ℂ × X => dslope (fun t => F t p.2) (P p.2) p.1) := by
  classical
  have hD := measurable_deriv_at_moving_center hF hP hd
  have hdiag : MeasurableSet {p : ℂ × X | p.1 = P p.2} :=
    measurableSet_eq_fun measurable_fst (hP.comp measurable_snd)
  have hQ : Measurable (fun p : ℂ × X =>
      (p.1 - P p.2)⁻¹ * (F p.1 p.2 - F (P p.2) p.2)) :=
    (measurable_fst.sub (hP.comp measurable_snd)).inv.mul
      (hF.sub (hF.comp ((hP.comp measurable_snd).prodMk measurable_snd)))
  have hi : Measurable (fun p : ℂ × X => if p.1 = P p.2 then
      deriv (fun t => F t p.2) (P p.2) else
      (p.1 - P p.2)⁻¹ * (F p.1 p.2 - F (P p.2) p.2)) :=
    Measurable.ite hdiag (hD.comp measurable_snd) hQ
  convert hi using 1
  funext p
  split_ifs with hp
  · simp only [hp, dslope_same]
  · rw [dslope_of_ne _ hp, slope_def_module, smul_eq_mul]

theorem dslope_eq_of_local_eq {f g : ℂ → ℂ} {P t : ℂ}
    (hnear : f =ᶠ[𝓝 P] g) (ht : f t = g t) : dslope f P t = dslope g P t := by
  by_cases h : t = P
  · subst t
    simpa only [dslope_same] using hnear.deriv_eq
  · rw [dslope_of_ne _ h, dslope_of_ne _ h, slope_def_module, slope_def_module,
      ht, hnear.eq_of_nhds]

theorem measurable_filledPoleNumerator {H F : ℂ → X → ℂ} {P : X → ℂ}
    (hH : Measurable (Function.uncurry H)) (hF : Measurable (Function.uncurry F))
    (hP : Measurable P) (hd : ∀ x, DifferentiableAt ℂ (fun t => F t x) (P x))
    (n : ℕ) :
    Measurable (fun p : ℂ × X =>
      filledPoleNumerator (fun t => H t p.2) (fun t => F t p.2) n (P p.2) p.1) := by
  have hA := measurable_dslope_moving_center hF hP hd
  have he : Measurable (fun p : ℂ × X => Complex.exp (-((n : ℂ) * F p.1 p.2))) :=
    Complex.continuous_exp.measurable.comp ((measurable_const.mul hF).neg)
  have hE : Measurable (fun p : ℂ × X => dslope Complex.exp 0 (-((n : ℂ) * F p.1 p.2))) :=
    (exponential_dslope_entire.continuous.measurable).comp ((measurable_const.mul hF).neg)
  exact (hH.mul (measurable_const.add he)).div ((measurable_const.mul hA).mul hE)

end
end IsingBulk.AnisoF002.NegativeHT
