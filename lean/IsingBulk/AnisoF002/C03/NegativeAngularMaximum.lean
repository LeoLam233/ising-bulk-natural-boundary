import IsingBulk.AnisoF002.C03.NegativeGaussianSymmetry
import IsingBulk.AnisoF002.C03.NegativeGaussianDensityBound
import IsingBulk.AnisoF002.C03.NegativeAngularRadialBounds

/-!
# The literal constrained angular maximum and a positive comparison

`angularZ` is exactly `n max_i theta_i^2` on the actual Euclidean unit
sphere in the zero-sum plane.  On the proved large-radius event its
exponential moment is bounded by a finite sum of coordinate excesses.
This positive comparison will be integrated against the actual Gaussian
law and its actual polar product; it does not assume concentration.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def planeMaxSquare {d : ℕ} (v : constrainedPlane d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (v : Ambient d) i ^ 2)

theorem coordinate_sq_le_max {d : ℕ} (v : constrainedPlane d) (i : Fin (d + 1)) :
    (v : Ambient d) i ^ 2 ≤ planeMaxSquare v := by
  unfold planeMaxSquare
  exact Finset.le_sup' (fun j => (v : Ambient d) j ^ 2) (Finset.mem_univ i)

theorem planeMaxSquare_nonneg {d : ℕ} (v : constrainedPlane d) : 0 ≤ planeMaxSquare v :=
  (sq_nonneg _).trans (coordinate_sq_le_max v 0)

theorem planeMaxSquare_attained {d : ℕ} (v : constrainedPlane d) :
    ∃ i : Fin (d + 1), planeMaxSquare v = (v : Ambient d) i ^ 2 := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    Finset.univ_nonempty (fun i => (v : Ambient d) i ^ 2)
  exact ⟨i, h⟩

theorem planeMaxSquare_le_quadratic {d : ℕ} (v : constrainedPlane d) :
    planeMaxSquare v ≤ ‖v‖ ^ 2 := by
  rw [constrained_norm_sq]
  apply Finset.sup'_le
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg ((v : Ambient d) j)) (Finset.mem_univ i)

theorem continuous_planeMaxSquare (d : ℕ) :
    Continuous (planeMaxSquare : constrainedPlane d → ℝ) := by
  unfold planeMaxSquare
  apply Continuous.finset_sup'_apply
  intro i _
  fun_prop

/-- Exactly the random variable in frozen F002 Lemma 4.2, with `n = d+1`. -/
def angularZ {d : ℕ} (θ : AngularSphere d) : ℝ :=
  ((d + 1 : ℕ) : ℝ) * planeMaxSquare θ.val

theorem angularZ_nonneg {d : ℕ} (θ : AngularSphere d) : 0 ≤ angularZ θ :=
  mul_nonneg (Nat.cast_nonneg _) (planeMaxSquare_nonneg _)

theorem angularZ_le_particle_number {d : ℕ} (θ : AngularSphere d) :
    angularZ θ ≤ ((d + 1 : ℕ) : ℝ) := by
  have h := planeMaxSquare_le_quadratic θ.val
  have hnorm : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  rw [hnorm, one_pow] at h
  simpa only [angularZ, mul_one] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (d + 1))

theorem continuous_angularZ (d : ℕ) : Continuous (angularZ : AngularSphere d → ℝ) :=
  continuous_const.mul ((continuous_planeMaxSquare d).comp continuous_subtype_val)

def momentProfile (z : ℝ) : ℝ := (1 + z) * Real.exp (z / 32)

theorem momentProfile_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ momentProfile z := by
  unfold momentProfile
  positivity

theorem momentProfile_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    momentProfile x ≤ momentProfile y := by
  unfold momentProfile
  apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith))
    (Real.exp_nonneg _) (by linarith)

theorem angular_moment_integrable {d : ℕ} (hd : 0 < d) :
    Integrable (fun θ : AngularSphere d => momentProfile (angularZ θ)) (angularLaw d) := by
  have := angularLaw_isProbability hd
  have hc : Continuous (fun θ : AngularSphere d => momentProfile (angularZ θ)) := by
    unfold momentProfile
    exact (continuous_const.add (continuous_angularZ d)).mul
      (Real.continuous_exp.comp ((continuous_angularZ d).div_const 32))
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

def coordinateExcess (n x : ℝ) : ℝ :=
  {x : ℝ | 16 * n ≤ x ^ 2}.indicator (fun x => momentProfile (8 * x ^ 2 / n)) x

theorem coordinateExcess_nonneg {n : ℝ} (hn : 0 ≤ n) (x : ℝ) :
    0 ≤ coordinateExcess n x := by
  apply Set.indicator_nonneg
  intro y _
  exact momentProfile_nonneg (div_nonneg (by positivity) hn)

theorem measurable_coordinateExcess (n : ℝ) : Measurable (coordinateExcess n) := by
  unfold coordinateExcess
  apply Measurable.indicator
  · unfold momentProfile
    fun_prop
  · exact (isClosed_le continuous_const (continuous_id.pow 2)).measurableSet

/-- Positive finite-coordinate majorant on the actual large-radius event. -/
theorem angular_moment_large_radius_pointwise {d : ℕ} (θ : AngularSphere d) (r : ℝ)
    (hQ : ((d + 1 : ℕ) : ℝ) ^ 2 / 8 ≤ r ^ 2) :
    momentProfile (angularZ θ) ≤ momentProfile 128 +
      ∑ i : Fin (d + 1), coordinateExcess ((d + 1 : ℕ) : ℝ)
        (((r • θ.val : constrainedPlane d) : Ambient d) i) := by
  have hn : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hsum : 0 ≤ ∑ i : Fin (d + 1), coordinateExcess ((d + 1 : ℕ) : ℝ)
      (((r • θ.val : constrainedPlane d) : Ambient d) i) :=
    Finset.sum_nonneg (fun _ _ => coordinateExcess_nonneg hn.le _)
  by_cases hz : angularZ θ ≤ 128
  · exact (momentProfile_mono (angularZ_nonneg θ) hz).trans (le_add_of_nonneg_right hsum)
  · have hz' : 128 < angularZ θ := lt_of_not_ge hz
    obtain ⟨i, hi⟩ := planeMaxSquare_attained θ.val
    have hscale : angularZ θ ≤ 8 * (r * (θ.val : Ambient d) i) ^ 2 /
        ((d + 1 : ℕ) : ℝ) := by
      apply (le_div_iff₀ hn).mpr
      rw [angularZ, hi]
      have hh := mul_nonneg (show 0 ≤ 8 * r ^ 2 - ((d + 1 : ℕ) : ℝ) ^ 2 by linarith)
        (sq_nonneg ((θ.val : Ambient d) i))
      nlinarith
    have hlarge : 16 * ((d + 1 : ℕ) : ℝ) ≤ (r * (θ.val : Ambient d) i) ^ 2 := by
      have hs := (le_div_iff₀ hn).mp hscale
      have hh := mul_nonneg hn.le (show 0 ≤ angularZ θ - 128 by linarith)
      nlinarith
    have hcoord : momentProfile (angularZ θ) ≤ coordinateExcess ((d + 1 : ℕ) : ℝ)
        (((r • θ.val : constrainedPlane d) : Ambient d) i) := by
      change momentProfile (angularZ θ) ≤ coordinateExcess ((d + 1 : ℕ) : ℝ)
        (r * (θ.val : Ambient d) i)
      rw [coordinateExcess, Set.indicator_of_mem
        (show r * (θ.val : Ambient d) i ∈ {x : ℝ | 16 * ((d + 1 : ℕ) : ℝ) ≤ x ^ 2} from hlarge)]
      exact momentProfile_mono (angularZ_nonneg θ) hscale
    have hsingle := Finset.single_le_sum
      (fun j _ => coordinateExcess_nonneg hn.le
        (((r • θ.val : constrainedPlane d) : Ambient d) j)) (Finset.mem_univ i)
    exact hcoord.trans (hsingle.trans (le_add_of_nonneg_left (momentProfile_nonneg (by norm_num))))

end
end IsingBulk.AnisoF002.NegativeHT.Angular
