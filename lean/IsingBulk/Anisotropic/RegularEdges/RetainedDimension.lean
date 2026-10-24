import IsingBulk.Anisotropic.RegularEdges.MatchedSummability
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Pi

/-! The retained-dimensional singular majorant. The unused angular variables are
integrated with a probability measure, so no dimension-dependent volume is lost. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace IsingBulk.Anisotropic.RegularEdges

/-- Normalized Lebesgue measure on the full angular period. -/
def edgeAngleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc (-Real.pi) Real.pi)

instance edgeAngleMeasure_probability : IsProbabilityMeasure edgeAngleMeasure := by
  constructor
  simp only [edgeAngleMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

/-- The first `m` coordinates of an `(m+k)`-fold probability product retain
exactly their original law. -/
theorem firstCoordinates_measurePreserving (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m k : ℕ) :
    MeasurePreserving (fun q : Fin (m + k) → ℝ => fun i : Fin m => q (Fin.castAdd k i))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  have h₁ := (measurePreserving_piCongrLeft (fun _ : Fin (m+k) => μ)
    (finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m + k))).symm
  have h₂ := measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin k => μ)
  have h₃ := measurePreserving_fst (μ := Measure.pi fun _ : Fin m => μ)
    (ν := Measure.pi fun _ : Fin k => μ)
  convert h₃.comp (h₂.comp h₁) using 1
  funext q i
  change q (Fin.castAdd k i) =
    (Equiv.piCongrLeft (fun _ : Fin (m+k) => ℝ) finSumFinEquiv).symm q (.inl i)
  simp

/-- The inverse-power singularity is integrable in the actual retained dimension
`2*j+3`, using the ordinary sup norm on its real coordinates. -/
theorem retainedPower_integrableOn (j : ℕ) :
    IntegrableOn (fun q : Fin (2 * j + 3) → ℝ => ‖q‖ ^ (-(2 * (j + 1) : ℝ)))
      (Set.univ.pi fun _ => Icc (-Real.pi) Real.pi) := by
  have hd : Module.finrank ℝ (Fin (2 * j + 3) → ℝ) = 2 * j + 3 := by simp
  have h := integrableOn_ball_of_norm_le_rpow (μ := volume)
    (E := Fin (2 * j + 3) → ℝ) (F := ℝ)
    (f := fun q => ‖q‖ ^ (-(2 * (j + 1) : ℝ)))
    (C := 1) (α := 2 * (j + 1)) (r := Real.pi + 1)
    (by rw [hd]; omega) (by rw [hd]; norm_num; linarith)
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg q) _)]
      simp)
    ((measurable_norm.pow_const _).aestronglyMeasurable)
  apply h.mono_set
  intro q hq
  rw [Metric.mem_ball, dist_zero_right]
  have hn : ‖q‖ ≤ Real.pi := by
    rw [pi_norm_le_iff_of_nonneg Real.pi_pos.le]
    intro i
    exact abs_le.mpr (hq i (by trivial))
  linarith

/-- The exact normalized product measure, with every angular normalization retained. -/
theorem edgeAngleMeasure_pi (m : ℕ) :
    Measure.pi (fun _ : Fin m => edgeAngleMeasure) =
      ((ENNReal.ofReal (2 * Real.pi))⁻¹)^m •
        volume.restrict (Set.univ.pi fun _ : Fin m => Icc (-Real.pi) Real.pi) := by
  rw [show (volume : Measure (Fin m → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi,
    edgeAngleMeasure]
  simp [Finset.prod_mul_distrib]

theorem retainedPower_integrable (j : ℕ) :
    Integrable (fun q : Fin (2 * j + 3) → ℝ => ‖q‖ ^ (-(2 * (j + 1) : ℝ)))
      (Measure.pi fun _ => edgeAngleMeasure) := by
  rw [edgeAngleMeasure_pi]
  exact (retainedPower_integrableOn j).smul_measure (by
    apply ENNReal.pow_ne_top
    exact ENNReal.inv_ne_top.mpr (by positivity))

/-- Uniform integrability after adjoining any number of unused angles. -/
theorem retainedPower_lift_integrable (j k : ℕ) :
    Integrable (fun q : Fin (2 * j + 3 + k) → ℝ =>
      ‖fun i : Fin (2 * j + 3) => q (Fin.castAdd k i)‖ ^ (-(2 * (j + 1) : ℝ)))
      (Measure.pi fun _ => edgeAngleMeasure) :=
  (firstCoordinates_measurePreserving edgeAngleMeasure (2*j+3) k).integrable_comp_of_integrable
    (retainedPower_integrable j)

instance edgeAngleMeasure_nullSingleton : NullSingletonClass edgeAngleMeasure := by
  constructor
  intro x
  simp only [edgeAngleMeasure, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton x), smul_eq_mul]
  rw [measure_mono_null Set.inter_subset_left (measure_singleton x), mul_zero]

 theorem firstCoordinates_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m k : ℕ) (f : (Fin m → ℝ) → ℝ) (hf : Integrable f (Measure.pi fun _ => μ)) :
    (∫ q : Fin (m+k) → ℝ, f (fun i => q (Fin.castAdd k i)) ∂Measure.pi (fun _ => μ)) =
      ∫ q : Fin m → ℝ, f q ∂Measure.pi (fun _ => μ) := by
  have h := firstCoordinates_measurePreserving μ m k
  have hm : AEStronglyMeasurable f (Measure.map
      (fun q : Fin (m+k) → ℝ => fun i : Fin m => q (Fin.castAdd k i))
      (Measure.pi fun _ => μ)) := by
    simpa only [h.map_eq] using hf.aestronglyMeasurable
  exact (integral_map h.measurable.aemeasurable hm).symm.trans (by rw [h.map_eq])

 theorem retainedPower_integral_lift (j k : ℕ) :
    (∫ q : Fin (2*j+3+k) → ℝ,
      ‖fun i : Fin (2*j+3) => q (Fin.castAdd k i)‖ ^ (-(2*(j+1):ℝ))
        ∂Measure.pi (fun _ => edgeAngleMeasure)) =
    ∫ q : Fin (2*j+3) → ℝ, ‖q‖ ^ (-(2*(j+1):ℝ))
      ∂Measure.pi (fun _ => edgeAngleMeasure) :=
  firstCoordinates_integral edgeAngleMeasure (2*j+3) k _ (retainedPower_integrable j)

end IsingBulk.Anisotropic.RegularEdges
