import IsingBulk.First.ShapeIntegrability

/-! Source-coordinate spellings and the post-mean-residue dominator. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

/-- The norm square is the source sum over all N dependent coordinates. -/
theorem shapePeriod_eq_sourceIntegral (n k : ℕ) (Q : ℝ) (c : ℂ) :
    shapePeriod n k Q c =
      ∫ t : Fin n → ℝ, ((firstVandermonde (shapeExtend t))^2 : ℝ) /
        ((Q : ℂ) + c * ((∑ i, (t i)^2) + (∑ i, t i)^2 : ℝ))^(k+1) := by
  unfold shapePeriod
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hnorm : (‖shapeCoordinateEquiv n (WithLp.toLp 2 t)‖ : ℂ)^2 =
      (((∑ i, (t i)^2) + (∑ i, t i)^2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, norm_sq_shapeCoordinateEquiv]
  dsimp only
  rw [hnorm]
  rfl

/-- The explicit constrained majorant used only after the physical mean residue. -/
def shapeMajorant {n : ℕ} (k : ℕ) (x : ShapeSpace n) : ℝ :=
  shapeVandermondeSq x / (1+‖x‖^2)^(k+1)

theorem shapeMajorant_integrable {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) : Integrable (@shapeMajorant n k) := by
  let f : ℝ → ℂ := fun r => (((1+r^2)^(k+1) : ℝ) : ℂ)⁻¹
  have hr : IntegrableOn (fun r : ℝ => (r ^ (n-1+(n+1)*n)) • f r) (Ioi 0) := by
    have hbase := (shapeRadialMajorant_integrable k).ofReal (𝕜 := ℂ)
    change Integrable (fun r : ℝ => ((r^(2*k)/(1+r^2)^(k+1) : ℝ) : ℂ)) at hbase
    simpa only [f, hdegree, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow,
      div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv] using hbase.integrableOn (s := Ioi 0)
  have hc : Integrable (fun x : ShapeSpace n => (shapeMajorant k x : ℂ)) := by
    simpa only [shapeMajorant, f, Complex.real_smul, Complex.ofReal_div,
      div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv] using integrable_shapeVandermonde_polar hn f hr
  simpa using hc.re

/-- Source free-coordinate form of the same parameter-independent majorant. -/
theorem shapeMajorant_coordinate_integrable {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) :
    Integrable (fun t : Fin n → ℝ => (firstVandermonde (shapeExtend t))^2 /
      (1 + (∑ i, (t i)^2) + (∑ i, t i)^2)^(k+1)) := by
  have hi := shapeMajorant_integrable hn hdegree
  have hc := (shapeCoordinateEquiv_measurePreserving n).integrable_comp_of_integrable hi
  have hz : ENNReal.ofReal (Real.sqrt (n+1 : ℝ)) ≠ 0 := by positivity
  have ht : ENNReal.ofReal (Real.sqrt (n+1 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hv := (integrable_smul_measure hz ht).mp hc
  have h := (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_of_integrable hv
  apply h.congr
  apply Filter.Eventually.of_forall
  intro t
  simp only [Function.comp_apply, shapeMajorant, norm_sq_shapeCoordinateEquiv]
  simp only [shapeVandermondeSq, shapeCoordinateEquiv_apply]
  congr 2
  ring

/-- Arithmetic source bridge for even N=n+1 and k=N²/2−1. -/
theorem source_shape_radial_exponent {n : ℕ} (hn : 1 ≤ n) (he : Even (n+1)) :
    n-1+(n+1)*n = 2*((n+1)^2/2-1) := by
  obtain ⟨p, hp⟩ := he.pow_of_ne_zero (show 2 ≠ 0 by decide)
  have hpoly : (n+1)^2 = (n+1)*n + (n+1) := by ring
  have hs : 2 ≤ (n+1)^2 := by nlinarith
  omega

end
end IsingBulk.First
