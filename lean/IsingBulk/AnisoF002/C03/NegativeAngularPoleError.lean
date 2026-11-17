import IsingBulk.AnisoF002.C03.NegativeAngularDisplacements
import IsingBulk.AnisoF002.C03.NegativeCentralScaling
import IsingBulk.AnisoF002.C03.NegativeAngularPerturbation

/-!
# Integration of the complete pole error over every constrained direction

The analytic density logarithm and the full cubic/quartic moving-pole
remainder are evaluated on the actual angular sphere.  The proved
exponential moment controls the entire sphere, including its exceptional
directions.  No angular cutoff or replacement density occurs here.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators

def angularQuadraticPole (d : ℕ) (τ : ℝ) (h : ℂ) (r : ℝ) : ℂ :=
  (τ : ℂ) + h * ((r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ)

theorem angular_quadratic_identity {d : ℕ} (τ : ℝ) (h : ℂ) (r : ℝ)
    (θ : AngularSphere d) :
    (τ : ℂ) + h * (∑ i, (angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i ^ 2) /
        (2 * ((d + 1 : ℕ) : ℂ)) = angularQuadraticPole d τ h r := by
  rw [angularComplexDisplacement_complex_square]
  unfold angularQuadraticPole
  push_cast
  ring

theorem angular_higher_error_bound {d : ℕ} {r Kp τ : ℝ} {h : ℂ}
    (hr : 0 ≤ r) (hKp : 0 ≤ Kp) (T : zeroSumDisplacements (d + 1) → ℂ)
    (θ : AngularSphere d)
    (herr : ‖T (angularComplexDisplacement r θ) -
      ((τ : ℂ) + h * (∑ i, (angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i ^ 2) /
        (2 * ((d + 1 : ℕ) : ℂ)))‖ ≤ Kp / ((d + 1 : ℕ) : ℝ) *
        ((∑ i, ‖(angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i‖ ^ 3) /
            ((d + 1 : ℕ) : ℝ) +
          (∑ i, ‖(angularComplexDisplacement r θ : Fin (d + 1) → ℂ) i‖ ^ 4) +
          displacementSquare (d + 1) (angularComplexDisplacement r θ) ^ 2 /
            ((d + 1 : ℕ) : ℝ))) :
    ‖T (angularComplexDisplacement r θ) - angularQuadraticPole d τ h r‖ ≤
      Kp / ((d + 1 : ℕ) : ℝ) *
        (r ^ 3 * Real.sqrt (angularZ θ) / Real.sqrt ((d + 1 : ℕ) : ℝ) /
            ((d + 1 : ℕ) : ℝ) +
          r ^ 4 * angularZ θ / ((d + 1 : ℕ) : ℝ) +
          r ^ 4 / ((d + 1 : ℕ) : ℝ)) := by
  rw [angular_quadratic_identity, angularComplexDisplacement_square, ← pow_mul] at herr
  apply herr.trans
  gcongr
  · exact angularComplexDisplacement_cubic hr θ
  · exact angularComplexDisplacement_quartic r θ

set_option maxHeartbeats 2000000 in
theorem complete_angular_pole_comparison {d k : ℕ} (hd : 2 ≤ d) (hk : 0 < k)
    {σ r A δ Kρ Kp τ : ℝ} {h : ℂ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp)
    (hKσ : 48 * Kp * σ ≤ 1) (hr : 0 ≤ r) (hrσ : r < σ)
    (hA : 1 ≤ A) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : δ ^ 2 = (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ))
    (hcentral : r ^ 2 ≤ A * ((d + 1 : ℕ) : ℝ) / (k : ℝ))
    (hsmall : 2 * A ^ 2 * (Kρ + Kp) * δ ≤ 1 / 32)
    (hτ : 0 < τ) (hτbound : 2 / (((d + 1 : ℕ) : ℝ)) ^ 2 ≤ τ)
    (hh : (1 / 2 : ℝ) ≤ h.re)
    (T ell : zeroSumDisplacements (d + 1) → ℂ)
    (hT : ∀ v : zeroSumDisplacements (d + 1),
      displacementSquare (d + 1) v < σ ^ 2 → AnalyticAt ℂ T v)
    (hella : ∀ v : zeroSumDisplacements (d + 1),
      displacementSquare (d + 1) v < σ ^ 2 → AnalyticAt ℂ ell v)
    (hell : ∀ v : zeroSumDisplacements (d + 1), displacementSquare (d + 1) v < σ ^ 2 →
      ‖ell v‖ ≤ Kρ * (Real.sqrt (((d + 1 : ℕ) : ℝ) * displacementSquare (d + 1) v) +
        ((d + 1 : ℕ) : ℝ) * displacementSquare (d + 1) v))
    (herr : ∀ v : zeroSumDisplacements (d + 1), displacementSquare (d + 1) v < σ ^ 2 →
      ‖T v - ((τ : ℂ) + h * (∑ i, (v : Fin (d + 1) → ℂ) i ^ 2) /
        (2 * ((d + 1 : ℕ) : ℂ)))‖ ≤ Kp / ((d + 1 : ℕ) : ℝ) *
        ((∑ i, ‖(v : Fin (d + 1) → ℂ) i‖ ^ 3) / ((d + 1 : ℕ) : ℝ) +
          (∑ i, ‖(v : Fin (d + 1) → ℂ) i‖ ^ 4) +
          displacementSquare (d + 1) v ^ 2 / ((d + 1 : ℕ) : ℝ))) :
    let D := τ + h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ))
    Integrable (fun θ : AngularSphere d =>
      Complex.exp (ell (angularComplexDisplacement r θ)) /
        T (angularComplexDisplacement r θ) ^ k) (angularLaw d) ∧
    ‖∫ θ : AngularSphere d,
      (Complex.exp (ell (angularComplexDisplacement r θ)) /
        T (angularComplexDisplacement r θ) ^ k -
        1 / angularQuadraticPole d τ h r ^ k) ∂angularLaw d‖ ≤
      angularPerturbationConstant * (2 * A ^ 2 * (Kρ + Kp)) * δ / D ^ k := by
  dsimp only
  have hN : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hQ (θ : AngularSphere d) :
      displacementSquare (d + 1) (angularComplexDisplacement r θ) < σ ^ 2 := by
    rw [angularComplexDisplacement_square]
    nlinarith
  let D := τ + h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ))
  have hD : 0 < D := by dsimp [D]; positivity
  have hDbound : 2 / (((d + 1 : ℕ) : ℝ)) ^ 2 ≤ D :=
    hτbound.trans (le_add_of_nonneg_right (by positivity))
  have hquarter (θ : AngularSphere d) :
      ‖T (angularComplexDisplacement r θ) - angularQuadraticPole d τ h r‖ ≤ D / 4 ∧
      D ≤ ‖angularQuadraticPole d τ h r‖ ∧ T (angularComplexDisplacement r θ) ≠ 0 := by
    have he := higher_pole_error_small (d + 1) (by omega) (angularComplexDisplacement r θ)
      hKp hσ hσ1 hKσ (hQ θ) (herr _ (hQ θ))
    rw [angular_quadratic_identity, angularComplexDisplacement_square] at he
    have hx := actual_pole_quarter_control hN hτ (sq_nonneg r) hh he
    exact ⟨hx.1, hx.2.1, hx.2.2.2⟩
  have hcT : Continuous (fun θ : AngularSphere d => T (angularComplexDisplacement r θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact (hT _ (hQ θ)).continuousAt.comp (continuous_angularComplexDisplacement d r).continuousAt
  have hcell : Continuous (fun θ : AngularSphere d => ell (angularComplexDisplacement r θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact (hella _ (hQ θ)).continuousAt.comp (continuous_angularComplexDisplacement d r).continuousAt
  have hcf : Continuous (fun θ : AngularSphere d =>
      Complex.exp (ell (angularComplexDisplacement r θ)) /
        T (angularComplexDisplacement r θ) ^ k) :=
    (Complex.continuous_exp.comp hcell).div (hcT.pow k)
      (fun θ => pow_ne_zero _ (hquarter θ).2.2)
  have := angularLaw_isProbability (show 0 < d by omega)
  refine ⟨hcf.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact, ?_⟩
  let E : AngularSphere d → ℝ := fun θ =>
    ‖ell (angularComplexDisplacement r θ)‖ +
      2 * (k : ℝ) * ‖T (angularComplexDisplacement r θ) - angularQuadraticPole d τ h r‖ / D
  have hcE : Continuous E := hcell.norm.add
    ((continuous_const.mul (hcT.sub continuous_const).norm).div_const D)
  have hE0 (θ : AngularSphere d) : 0 ≤ E θ := by dsimp [E]; positivity
  have hEb (θ : AngularSphere d) :
      E θ ≤ (2 * A ^ 2 * (Kρ + Kp) * δ) * (1 + angularZ θ) := by
    apply central_full_error_profile hN hkR hA hr hδ hδ1 hscale hcentral
      (angularZ_nonneg θ) hKρ hKp (norm_nonneg _) hDbound
    · simpa only [angularComplexDisplacement_square] using hell _ (hQ θ)
    · exact angular_higher_error_bound hr hKp T θ (herr _ (hQ θ))
  have hη : 0 ≤ 2 * A ^ 2 * (Kρ + Kp) * δ := by positivity
  obtain ⟨hEi, hI⟩ := uniform_angular_dominated_perturbation hd hη hsmall
    hcE.aestronglyMeasurable hE0 hEb
  have hb := norm_integral_le_of_norm_le (hEi.div_const (D ^ k))
    (Filter.Eventually.of_forall (fun θ : AngularSphere d =>
      complete_pole_integrand_error k (ell (angularComplexDisplacement r θ))
        (T (angularComplexDisplacement r θ)) (angularQuadraticPole d τ h r) D
        hD (hquarter θ).2.1 (hquarter θ).1))
  rw [integral_div] at hb
  calc
    _ ≤ (∫ θ : AngularSphere d, (Real.exp (E θ) - 1) ∂angularLaw d) / D ^ k := hb
    _ ≤ (angularPerturbationConstant * (2 * A ^ 2 * (Kρ + Kp) * δ)) / D ^ k := by
      exact div_le_div_of_nonneg_right hI (by positivity)
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT.Angular
