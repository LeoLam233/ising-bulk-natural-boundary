import IsingBulk.AnisoF002.C03.NegativeGaussianMarginalRatio

/-!
# The actual first-coordinate density of the constrained Gaussian law

The formula is obtained by pushing the previously proved unit-Jacobian
chart through the literal Gaussian measure and applying Tonelli.  Its
inner expectation is against the actual smaller constrained Gaussian
law.  No marginal-density identity is supplied as an assumption.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def gaussianMarginalPlaneEquiv (d : ℕ) :
    (ℝ × constrainedPlane d) ≃ᵐ constrainedPlane (d + 1) :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    (independentChart d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.symm).trans
      (gaussianMarginalEquiv d)

theorem gaussianMarginalPlaneEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (gaussianMarginalPlaneEquiv d)
      (volume.prod (independentMeasure d)) (independentMeasure (d + 1)) := by
  have hi := MeasurePreserving.symm
    (independentChart d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
    (independentChart_measurePreserving d)
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod hi
  have he := gaussianMarginalEquiv_measurePreserving d
  rw [Measure.volume_eq_prod] at he
  exact he.comp hp

theorem gaussianMarginalPlaneEquiv_apply (d : ℕ) (x : ℝ) (u : constrainedPlane d) :
    (gaussianMarginalPlaneEquiv d (x, u) : Ambient (d + 1)) =
      WithLp.toLp 2 (Fin.cons x
        (fun i => (u : Ambient d) i - x / ((d + 1 : ℕ) : ℝ))) := by
  have h := gaussianMarginalEquiv_apply d x ((independentChart d).symm u)
  change (gaussianMarginalEquiv d (x, (independentChart d).symm u) : Ambient (d + 1)) = _
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem gaussianWeight_planeMarginal (d : ℕ) (x : ℝ) (u : constrainedPlane d) :
    gaussianWeight (gaussianMarginalPlaneEquiv d (x, u)) =
      Real.exp (-marginalScale d * x ^ 2) * gaussianWeight u *
        ∏ i, (marginalScale d * x - (u : Ambient d) i) ^ 2 := by
  have h := gaussianWeight_marginal d x ((independentChart d).symm u)
  change gaussianWeight (gaussianMarginalEquiv d (x, (independentChart d).symm u)) = _
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem gaussianLaw_withDensity (d : ℕ) :
    gaussianLaw d = (independentMeasure d).withDensity
      (fun v => ENNReal.ofReal (gaussianWeight v / constrainedGaussianIntegral d)) := by
  rw [gaussianLaw, gaussianMeasure_mass_exact, gaussianMeasure,
    ← withDensity_smul _ (continuous_gaussianWeight d).measurable.ennreal_ofReal]
  congr 1
  funext v
  change (ENNReal.ofReal (constrainedGaussianIntegral d))⁻¹ *
    ENNReal.ofReal (gaussianWeight v) = _
  rw [ENNReal.ofReal_div_of_pos (constrainedGaussianIntegral_pos d), div_eq_mul_inv, mul_comm]

theorem gaussianLaw_integrable_iff_weighted (d : ℕ) (f : constrainedPlane d → ℝ) :
    Integrable f (gaussianLaw d) ↔
      Integrable (fun v => gaussianWeight v * f v) (independentMeasure d) := by
  rw [gaussianLaw, integrable_inv_smul_measure]
  · rw [gaussianMeasure, integrable_withDensity_iff_integrable_smul'
      (continuous_gaussianWeight d).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (gaussianWeight_nonneg _), smul_eq_mul]
  · rw [gaussianMeasure_mass_exact]
    exact (ENNReal.ofReal_pos.mpr (constrainedGaussianIntegral_pos d)).ne'
  · rw [gaussianMeasure_mass_exact]
    exact ENNReal.ofReal_ne_top

theorem gaussianWeight_planeMarginal_integrable {d : ℕ} (hd : 0 < d) (x : ℝ) :
    Integrable (fun u : constrainedPlane d =>
      gaussianWeight (gaussianMarginalPlaneEquiv d (x, u))) (independentMeasure d) := by
  have h := (gaussianLaw_integrable_iff_weighted d _).mp (marginal_insertion_integrable hd x)
  simpa only [gaussianWeight_planeMarginal, mul_assoc] using
    h.const_mul (Real.exp (-marginalScale d * x ^ 2))

/-- The complete marginal, including the neighboring Mehta normalization ratio. -/
def gaussianMarginalDensity (d : ℕ) (x : ℝ) : ℝ :=
  constrainedGaussianIntegral d / constrainedGaussianIntegral (d + 1) *
    Real.exp (-marginalScale d * x ^ 2) *
      ∫ u : constrainedPlane d,
        ∏ i, (marginalScale d * x - (u : Ambient d) i) ^ 2 ∂gaussianLaw d

theorem gaussianMarginalDensity_nonneg (d : ℕ) (x : ℝ) :
    0 ≤ gaussianMarginalDensity d x := by
  unfold gaussianMarginalDensity
  apply mul_nonneg (mul_nonneg
    (div_nonneg (constrainedGaussianIntegral_pos _).le (constrainedGaussianIntegral_pos _).le)
    (Real.exp_nonneg _))
  exact integral_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => sq_nonneg _))

theorem gaussianMarginalDensity_raw (d : ℕ) (x : ℝ) :
    gaussianMarginalDensity d x =
      (∫ u : constrainedPlane d,
        gaussianWeight (gaussianMarginalPlaneEquiv d (x, u)) ∂independentMeasure d) /
          constrainedGaussianIntegral (d + 1) := by
  unfold gaussianMarginalDensity
  rw [gaussianLaw_integral_weighted]
  simp_rw [gaussianWeight_planeMarginal, mul_assoc]
  rw [integral_const_mul]
  have hG : constrainedGaussianIntegral d ≠ 0 := (constrainedGaussianIntegral_pos d).ne'
  field_simp

theorem map_fst_withDensity_integral
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (g : X × Y → ℝ≥0∞) (hg : Measurable g) :
    ((μ.prod ν).withDensity g).map Prod.fst =
      μ.withDensity (fun x => ∫⁻ y, g (x, y) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs]
  have hp : Prod.fst ⁻¹' s = s ×ˢ (univ : Set Y) := by ext z; simp
  rw [hp, setLIntegral_prod g hg.aemeasurable]
  simp only [Measure.restrict_univ]

/-- Tonelli's actual first-coordinate marginal, with the density from the frozen proof. -/
theorem gaussianLaw_first_coordinate_density {d : ℕ} (hd : 0 < d) :
    (gaussianLaw (d + 1)).map (fun v : constrainedPlane (d + 1) => (v : Ambient (d + 1)) 0) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianMarginalDensity d x)) := by
  let e := gaussianMarginalPlaneEquiv d
  let f : constrainedPlane (d + 1) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (gaussianWeight v / constrainedGaussianIntegral (d + 1))
  have hf : Measurable f :=
    ((continuous_gaussianWeight (d + 1)).div_const _).measurable.ennreal_ofReal
  have hm : ((volume.prod (independentMeasure d)).withDensity (fun z => f (e z))).map e =
      gaussianLaw (d + 1) := by
    rw [measurableEquiv_map_withDensity_comp e _ f hf,
      (gaussianMarginalPlaneEquiv_measurePreserving d).map_eq, gaussianLaw_withDensity]
  have heq : (fun v : constrainedPlane (d + 1) => (v : Ambient (d + 1)) 0) ∘ e =
      Prod.fst := by
    funext z
    rcases z with ⟨x, u⟩
    change (gaussianMarginalPlaneEquiv d (x, u) : Ambient (d + 1)) 0 = x
    rw [gaussianMarginalPlaneEquiv_apply]
    rfl
  rw [← hm, Measure.map_map (by fun_prop) e.measurable, heq]
  rw [map_fst_withDensity_integral (volume : Measure ℝ) (independentMeasure d)
    (fun z => f (e z)) (hf.comp e.measurable)]
  congr 1
  funext x
  change (∫⁻ u, ENNReal.ofReal
    (gaussianWeight (gaussianMarginalPlaneEquiv d (x, u)) /
      constrainedGaussianIntegral (d + 1)) ∂independentMeasure d) = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((gaussianWeight_planeMarginal_integrable hd x).div_const _)
    (Filter.Eventually.of_forall (fun u =>
      div_nonneg (gaussianWeight_nonneg _) (constrainedGaussianIntegral_pos _).le)),
    integral_div, ← gaussianMarginalDensity_raw]

end
end IsingBulk.AnisoF002.NegativeHT.Angular
