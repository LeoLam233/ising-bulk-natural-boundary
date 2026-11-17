import IsingBulk.AnisoF002.C03.NegativeAngularMoments
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual constrained Gaussian radial expectations

The Gamma moments are transported back from the constructed polar
product to the literal Gaussian Vandermonde probability on the
zero-sum plane.  The finite moment bound is the one required by the
AM--GM marginal estimate in frozen F002, Lemma 4.2.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem gaussianLaw_nullSingleton {d : ℕ} (hd : 0 < d) :
    NullSingletonClass (gaussianLaw d) := by
  obtain ⟨v, hv, _⟩ := exists_planeVandermonde_pos hd
  let : Nontrivial (constrainedPlane d) := ⟨⟨v, 0, hv⟩⟩
  refine ⟨fun x => ?_⟩
  rw [gaussianLaw, Measure.smul_apply]
  have hz : gaussianMeasure d {x} = 0 :=
    withDensity_absolutelyContinuous _ _ (measure_singleton x)
  rw [hz, smul_zero]

theorem gaussianLaw_integral_norm {d : ℕ} (hd : 0 < d) (f : ℝ → ℝ) :
    (∫ v : constrainedPlane d, f ‖v‖ ∂gaussianLaw d) =
      ∫ r : Ioi (0 : ℝ), f r.val ∂radialLaw d := by
  have := gaussianLaw_nullSingleton hd
  have := angularLaw_isProbability hd
  calc
    (∫ v : constrainedPlane d, f ‖v‖ ∂gaussianLaw d) =
        ∫ v : ({0}ᶜ : Set (constrainedPlane d)), f ‖v.val‖
          ∂(gaussianLaw d).comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl (fun v => f ‖v‖),
        restrict_compl_singleton]
    _ = ∫ z : AngularSphere d × Ioi (0 : ℝ), f z.2.val
        ∂(angularLaw d).prod (radialLaw d) := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_apply_snd_coe] using
        (gaussianLaw_polar_measurePreserving hd).integral_comp
          (homeomorphUnitSphereProd (constrainedPlane d)).measurableEmbedding
          (fun z => f z.2.val)
    _ = ∫ r : Ioi (0 : ℝ), f r.val ∂radialLaw d := by
      rw [integral_fun_snd (fun r : Ioi (0 : ℝ) => f r.val)]
      simp

theorem gaussianLaw_quadratic_moment {d : ℕ} (hd : 0 < d) (k : ℕ) :
    (∫ v : constrainedPlane d, (‖v‖ ^ 2) ^ k ∂gaussianLaw d) =
      ∏ j ∈ Finset.range k, (radialShape d + j) := by
  rw [gaussianLaw_integral_norm hd (fun r => (r ^ 2) ^ k),
    radialLaw_quadratic_moment]

theorem gaussianLaw_quadratic_moment_integrable {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Integrable (fun v : constrainedPlane d => (‖v‖ ^ 2) ^ k) (gaussianLaw d) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianLaw_quadratic_moment hd]
  exact (Finset.prod_pos (fun j _ => add_pos_of_pos_of_nonneg (radialShape_pos d)
    (Nat.cast_nonneg j))).ne'

/-- All the scaled moments needed in the one-coordinate marginal, uniformly in `k ≤ m`. -/
theorem gaussianLaw_scaled_quadratic_moment_le {d : ℕ} (hd : 0 < d)
    {k : ℕ} (hk : k ≤ d + 1) :
    (∫ v : constrainedPlane d,
      (‖v‖ ^ 2 / ((d + 1 : ℕ) : ℝ)) ^ k ∂gaussianLaw d) ≤
      ((d + 2 : ℕ) : ℝ) ^ k := by
  have hm : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  simp_rw [div_pow]
  rw [integral_div, gaussianLaw_quadratic_moment hd]
  calc
    (∏ j ∈ Finset.range k, (radialShape d + j)) / ((d + 1 : ℕ) : ℝ) ^ k =
        ∏ j ∈ Finset.range k, ((radialShape d + j) / ((d + 1 : ℕ) : ℝ)) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ ∏ _j ∈ Finset.range k, ((d + 2 : ℕ) : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact div_nonneg (add_nonneg (radialShape_pos d).le (Nat.cast_nonneg j)) hm.le
      · intro j hj
        rw [div_le_iff₀ hm, radialShape_exact hd]
        have hj' : (j : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast (show j ≤ d by have := Finset.mem_range.mp hj; omega)
        push_cast
        have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith [sq_nonneg (d : ℝ)]
    _ = ((d + 2 : ℕ) : ℝ) ^ k := by simp

end
end IsingBulk.AnisoF002.NegativeHT.Angular
