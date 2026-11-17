import IsingBulk.AnisoF002.C03.NegativeAngularMaximum

/-!
# An integrable Gaussian majorant for the full angular moment

The exact all-coordinate marginal density makes each coordinate excess
cost at most `1/n` times one fixed integrable Gaussian envelope.  Summing
over all `n` physical coordinates cancels that factor.  The resulting
constant is independent of particle number and will be transported through
the actual polar product to establish the angular moment.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def gaussianMomentEnvelope (x : ℝ) : ℝ := (1 + 8 * x ^ 2) * Real.exp (-x ^ 2 / 4)

theorem gaussianMomentEnvelope_nonneg (x : ℝ) : 0 ≤ gaussianMomentEnvelope x := by
  unfold gaussianMomentEnvelope
  positivity

theorem gaussianMomentEnvelope_integrable : Integrable gaussianMomentEnvelope := by
  have h0 := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 := integrable_rpow_mul_exp_neg_mul_sq (show (0 : ℝ) < 1 / 4 by norm_num)
    (show (-1 : ℝ) < 2 by norm_num)
  simp only [Real.rpow_two] at h2
  convert h0.fun_add (h2.const_mul 8) using 1
  funext x
  unfold gaussianMomentEnvelope
  rw [show -(1 / 4 : ℝ) * x ^ 2 = -x ^ 2 / 4 by ring]
  ring

def gaussianMomentConstant : ℝ := ∫ x : ℝ, gaussianMomentEnvelope x

theorem gaussianMomentConstant_nonneg : 0 ≤ gaussianMomentConstant :=
  integral_nonneg gaussianMomentEnvelope_nonneg

theorem measurable_gaussianMarginalDensity {d : ℕ} (hd : 0 < d) :
    Measurable (gaussianMarginalDensity d) := by
  have := gaussianLaw_isProbability hd
  have hm : StronglyMeasurable (Function.uncurry (fun x : ℝ => fun u : constrainedPlane d =>
      ∏ i, (marginalScale d * x - (u : Ambient d) i) ^ 2)) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  have hi := (hm.integral_prod_right (ν := gaussianLaw d)).measurable
  unfold gaussianMarginalDensity
  exact ((measurable_const.div_const _).mul (by fun_prop)).mul hi

theorem density_mul_coordinateExcess_le {d : ℕ} (hd : 0 < d) (x : ℝ) :
    gaussianMarginalDensity d x * coordinateExcess ((d + 2 : ℕ) : ℝ) x ≤
      gaussianMomentEnvelope x / ((d + 2 : ℕ) : ℝ) := by
  let n : ℝ := ((d + 2 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ d + 2 by omega)
  by_cases hx : 16 * n ≤ x ^ 2
  · rw [coordinateExcess, Set.indicator_of_mem (show x ∈ {x : ℝ | 16 * n ≤ x ^ 2} from hx)]
    have hsmall : x ^ 2 / n ≤ x ^ 2 := by
      apply (div_le_iff₀ hn).mpr
      nlinarith [sq_nonneg x]
    calc
      gaussianMarginalDensity d x * momentProfile (8 * x ^ 2 / n) ≤
          ((1 / n) * Real.exp (-x ^ 2 / 2)) * momentProfile (8 * x ^ 2 / n) :=
        mul_le_mul_of_nonneg_right (gaussianMarginalDensity_tail hd x hx)
          (momentProfile_nonneg (by positivity))
      _ = (1 / n) * (1 + 8 * (x ^ 2 / n)) *
          Real.exp (-x ^ 2 / 2 + (x ^ 2 / n) / 4) := by
        unfold momentProfile
        rw [show 8 * x ^ 2 / n / 32 = (x ^ 2 / n) / 4 by ring, Real.exp_add]
        ring
      _ ≤ (1 / n) * (1 + 8 * x ^ 2) * Real.exp (-x ^ 2 / 4) := by
        apply mul_le_mul _ (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) (by positivity)
        gcongr
      _ = _ := by unfold gaussianMomentEnvelope; ring
  · rw [coordinateExcess, Set.indicator_of_notMem (show x ∉ {x : ℝ | 16 * n ≤ x ^ 2} from hx), mul_zero]
    exact div_nonneg (gaussianMomentEnvelope_nonneg _) hn.le

theorem density_mul_coordinateExcess_integrable {d : ℕ} (hd : 0 < d) :
    Integrable (fun x => gaussianMarginalDensity d x *
      coordinateExcess ((d + 2 : ℕ) : ℝ) x) := by
  apply (gaussianMomentEnvelope_integrable.div_const ((d + 2 : ℕ) : ℝ)).mono'
    (((measurable_gaussianMarginalDensity hd).mul (measurable_coordinateExcess _)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (gaussianMarginalDensity_nonneg _ _)
    (coordinateExcess_nonneg (by positivity) _))]
  exact density_mul_coordinateExcess_le hd x

theorem coordinateExcess_integrable_gaussian {d : ℕ} (hd : 0 < d) (i : Fin (d + 2)) :
    Integrable (fun v : constrainedPlane (d + 1) =>
      coordinateExcess ((d + 2 : ℕ) : ℝ) ((v : Ambient (d + 1)) i)) (gaussianLaw (d + 1)) := by
  have hw : Integrable (coordinateExcess ((d + 2 : ℕ) : ℝ))
      (volume.withDensity (fun x => ENNReal.ofReal (gaussianMarginalDensity d x))) := by
    rw [integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianMarginalDensity hd).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (gaussianMarginalDensity_nonneg _ _), smul_eq_mul] using
      density_mul_coordinateExcess_integrable hd
  have hp : MeasurePreserving (fun v : constrainedPlane (d + 1) => (v : Ambient (d + 1)) i)
      (gaussianLaw (d + 1))
      (volume.withDensity (fun x => ENNReal.ofReal (gaussianMarginalDensity d x))) :=
    ⟨by fun_prop, gaussianLaw_coordinate_density hd i⟩
  exact hp.integrable_comp_of_integrable hw

theorem coordinateExcess_gaussian_integral_le {d : ℕ} (hd : 0 < d) (i : Fin (d + 2)) :
    (∫ v : constrainedPlane (d + 1),
      coordinateExcess ((d + 2 : ℕ) : ℝ) ((v : Ambient (d + 1)) i) ∂gaussianLaw (d + 1)) ≤
        gaussianMomentConstant / ((d + 2 : ℕ) : ℝ) := by
  rw [← integral_map_of_stronglyMeasurable (by fun_prop)
    (measurable_coordinateExcess ((d + 2 : ℕ) : ℝ)).stronglyMeasurable,
    gaussianLaw_coordinate_density hd i,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_gaussianMarginalDensity hd).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianMarginalDensity_nonneg _ _), smul_eq_mul]
  have h := integral_mono (density_mul_coordinateExcess_integrable hd)
    (gaussianMomentEnvelope_integrable.div_const ((d + 2 : ℕ) : ℝ))
    (density_mul_coordinateExcess_le hd)
  simpa only [integral_div, gaussianMomentConstant] using h

def gaussianMomentMajorant {d : ℕ} (v : constrainedPlane d) : ℝ :=
  momentProfile 128 + ∑ i : Fin (d + 1), coordinateExcess ((d + 1 : ℕ) : ℝ) ((v : Ambient d) i)

theorem gaussianMomentMajorant_nonneg {d : ℕ} (v : constrainedPlane d) :
    0 ≤ gaussianMomentMajorant v := by
  exact add_nonneg (momentProfile_nonneg (by norm_num))
    (Finset.sum_nonneg (fun _ _ => coordinateExcess_nonneg (by positivity) _))

theorem gaussianMomentMajorant_integrable {d : ℕ} (hd : 2 ≤ d) :
    Integrable (gaussianMomentMajorant : constrainedPlane d → ℝ) (gaussianLaw d) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hk : 0 < k := by omega
  have := gaussianLaw_isProbability (show 0 < k + 1 by omega)
  exact (integrable_const _).fun_add (integrable_finsetSum _
    (fun i _ => coordinateExcess_integrable_gaussian hk i))

/-- Every particle coordinate is included, and its `1/n` cost cancels in the complete sum. -/
theorem gaussianMomentMajorant_integral_le {d : ℕ} (hd : 2 ≤ d) :
    (∫ v : constrainedPlane d, gaussianMomentMajorant v ∂gaussianLaw d) ≤
      momentProfile 128 + gaussianMomentConstant := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hk : 0 < k := by omega
  have := gaussianLaw_isProbability (show 0 < k + 1 by omega)
  unfold gaussianMomentMajorant
  rw [integral_add (integrable_const _)
    (integrable_finsetSum _ (fun i _ => coordinateExcess_integrable_gaussian hk i)),
    integral_finsetSum Finset.univ (fun i _ => coordinateExcess_integrable_gaussian hk i)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  apply add_le_add_right
  calc
    _ ≤ ∑ _i : Fin (k + 2), gaussianMomentConstant / ((k + 2 : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun i _ => coordinateExcess_gaussian_integral_le hk i)
    _ = gaussianMomentConstant := by simp; field_simp

end
end IsingBulk.AnisoF002.NegativeHT.Angular
