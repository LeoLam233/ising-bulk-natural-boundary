import IsingBulk.AnisoF002.C03.RegularCollisionJetLimit
import IsingBulk.AnisoF002.C03.RegularEdgeDensityMajorant

/-!
# Uniform local collision bounds with the inward temperature retained

The complete phase attenuation retains epsilon as well as the full
quadratic angular sum.  Cauchy's estimate applies to the actual filled
numerator times the full rational kernel.  For each fixed resonant N this
gives the denominator (epsilon+Q)^(j+1) required by dominated scaling.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem full_principal_attenuation {N : ℕ} (hN : 0 < N) {eps : ℝ}
    (he : 0 < eps) (he0 : eps ≤ d.eps0) (x : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ Real.pi) :
    d.kappa * (eps + angularQuadratic x) ≤
      (edgeTotalPhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) x).re := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
    (fun i _ => d.attenuation eps he he0 (x i) (hx i))
  have hsum' : d.kappa * ((N : ℝ) * eps + angularQuadratic x) ≤
      (edgeTotalPhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) x).re := by
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, edgeTotalPhase,
      Complex.re_sum, angularQuadratic] using hsum
  apply le_trans _ hsum'
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact mul_le_mul_of_nonneg_left (by nlinarith) d.kappa_pos.le

theorem fullDensity_principal_jet_bound {N : ℕ} (hN : 0 < N) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 → eps ≤ 1 →
      ∀ x : Fin N → ℝ, (∀ i, |x i| ≤ Real.pi) →
        ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x)
          ((eps : ℂ) * Complex.I)‖ ≤
          C * retainedSineBlock x / (eps + angularQuadratic x) ^ (j + 1) := by
  let E := d.retainedEvenEnvelope N 0 + 1
  let K := min d.kappa (1 / (1 + (N : ℝ) * Real.pi ^ 2))
  let C₀ := d.densityJetConstant j * (N : ℝ) ^ j * E
  have hE : 0 < E := by dsimp [E]; linarith [d.retainedEvenEnvelope_nonneg N 0]
  have hK : 0 < K := lt_min d.kappa_pos (by positivity)
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    exact mul_pos (mul_pos (d.densityJetConstant_pos j) (pow_pos (by exact_mod_cast hN) _)) hE
  refine ⟨C₀ / K ^ (j + 1), div_pos hC₀ (pow_pos hK _), ?_⟩
  intro eps he he0 he1 x hx
  let P := eps + angularQuadratic x
  let eta := min 1 (d.kappa * P)
  have hP : 0 < P := add_pos_of_pos_of_nonneg he (angularQuadratic_nonneg x)
  have heta : 0 < eta := lt_min zero_lt_one (mul_pos d.kappa_pos hP)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hG : eta ≤ (edgeTotalPhase (affineEdgeCenter b) a ((eps : ℂ) * Complex.I) x).re :=
    (min_le_right _ _).trans (d.full_principal_attenuation hN he he0 x hx)
  have hQ : angularQuadratic x ≤ (N : ℝ) * Real.pi ^ 2 := by
    have hq (i : Fin N) : x i ^ 2 ≤ Real.pi ^ 2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg (x i)) (hx i) 2
      simpa only [sq_abs] using hh
    simpa only [angularQuadratic, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hq i)
  have hKP : K * P ≤ eta := by
    apply le_min
    · calc
        K * P ≤ (1 / (1 + (N : ℝ) * Real.pi ^ 2)) * P :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hP.le
        _ ≤ (1 / (1 + (N : ℝ) * Real.pi ^ 2)) * (1 + (N : ℝ) * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left (by dsimp [P]; linarith) (by positivity)
        _ = 1 := one_div_mul_cancel (by positivity)
    · exact mul_le_mul_of_nonneg_right (min_le_left _ _) hP.le
  have hnum : ∀ u ∈ Metric.closedBall (0 : ℂ) d.numerator.radius,
      ‖edgeRetainedNumerator N (affineEdgeCenter b) a u x‖ ≤ E := by
    intro u hu
    have hh := d.numerator.retainedNumerator_even_bound (m := N) hu 0 x
    change ‖edgeRetainedNumerator N (affineEdgeCenter b) a u x‖ ≤ d.retainedEvenEnvelope N 0 at hh
    exact hh.trans (by dsimp [E]; linarith)
  have hjet := d.fullDensity_retained_jet_bound (m := N) (N := 0) x hN heta heta1
    (d.inward_mem eps he he0) hG hnum j
  change ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x)
    ((eps : ℂ) * Complex.I)‖ ≤ retainedSineBlock x *
      (j.factorial * (E * (8 / eta)) / (d.phase.siteRadius N eta) ^ j) at hjet
  have harith : retainedSineBlock x *
      (j.factorial * (E * (8 / eta)) / (d.phase.siteRadius N eta) ^ j) =
      C₀ * retainedSineBlock x / eta ^ (j + 1) := by
    dsimp [C₀, densityJetConstant, RegularEdgePhaseControl.siteRadius]
    rw [mul_pow, div_pow, pow_succ]
    field_simp
  rw [harith] at hjet
  calc
    ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u x)
        ((eps : ℂ) * Complex.I)‖ ≤ C₀ * retainedSineBlock x / eta ^ (j + 1) := hjet
    _ ≤ C₀ * retainedSineBlock x / (K * P) ^ (j + 1) :=
      div_le_div_of_nonneg_left (mul_nonneg hC₀.le (retainedSineBlock_nonneg x))
        (pow_pos (mul_pos hK hP) _) (pow_le_pow_left₀ (mul_nonneg hK.le hP.le) hKP _)
    _ = (C₀ / K ^ (j + 1)) * retainedSineBlock x / (eps + angularQuadratic x) ^ (j + 1) := by
      rw [mul_pow]
      dsimp [P]
      field_simp

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
