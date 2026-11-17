import IsingBulk.AnisoF002.C03.RegularScaledCollision
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence for the complete constrained collision integral

The integration domain expands under the actual real change of scale.
Every fixed point eventually lies in that domain.  The complete scaled
temperature jets admit one integrable Vandermonde majorant, so their
limits pass through the actual independent-coordinate Lebesgue integral.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def collisionScaledLocal {n : ℕ} (b : ℝ) (a : ℂ → ℂ) (j : ℕ) (delta s : ℝ)
    (q : Fin n → ℝ) : ℂ :=
  if ‖s • q‖ < delta then collisionScaledJet b a j s (flatConstrainedAngles q) else 0

theorem collisionScaledLocal_limit {n : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (d : RegularEdgeControl (affineEdgeCenter b) a) (hb : |b| < 1) (ha : 0 < (a 0).im)
    (hres : upperEdgeRoot (b : ℂ) ^ (n + 1) = 1) {delta : ℝ} (hd : 0 < delta)
    (q : Fin n → ℝ) (j : ℕ) :
    Tendsto (fun s : ℝ => collisionScaledLocal b a j delta s q) (𝓝[>] (0 : ℝ))
      (𝓝 (collisionLeadingJet b a j (flatConstrainedAngles q))) := by
  have hnorm : ContinuousAt (fun s : ℝ => ‖s • q‖) 0 := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ‖s • q‖ < delta :=
    hnorm.eventually (gt_mem_nhds (by simpa using hd))
  apply (collisionScaledJet_limit d (Nat.succ_pos n) hb ha hres (flatConstrainedAngles q) j).congr'
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds] with s hs
  simp only [collisionScaledLocal, ite_eq_left hs]

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem collisionScaledJet_continuous {N : ℕ} (hN : 0 < N) (j : ℕ)
    {s : ℝ} (hs : 0 < s) (hs0 : s ^ 2 ≤ d.eps0) :
    Continuous (collisionScaledJet (N := N) b a j s) := by
  have hc := d.fullDensity_jet_continuous_inward hN (sq_pos_of_pos hs) hs0 j
  have hm : Continuous (fun x : Fin N → ℝ => fun i => s * x i) := by fun_prop
  exact continuous_const.mul (hc.comp hm)

theorem collisionScaledLocal_measurable {n : ℕ} (j : ℕ) (delta : ℝ)
    {s : ℝ} (hs : 0 < s) (hs0 : s ^ 2 ≤ d.eps0) :
    Measurable (collisionScaledLocal (n := n) b a j delta s) := by
  have hcn : Continuous (fun q : Fin n → ℝ => ‖s • q‖) := by fun_prop
  have hset : MeasurableSet {q : Fin n → ℝ | ‖s • q‖ < delta} :=
    (isOpen_lt hcn continuous_const).measurableSet
  exact Measurable.ite hset
    (((d.collisionScaledJet_continuous (Nat.succ_pos n) j hs hs0).comp
      (flatConstrainedAngles_continuous n)).measurable) measurable_const

theorem collisionScaledLocal_bound {n : ℕ} (j : ℕ) {delta : ℝ}
    (hd : delta ≤ Real.pi / ((n : ℝ) + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → s ^ 2 ≤ d.eps0 → s ^ 2 ≤ 1 →
      ∀ q : Fin n → ℝ,
        ‖collisionScaledLocal b a j delta s q‖ ≤ C * collisionRationalMajorant n (j + 1) q := by
  obtain ⟨C, hC, hbound⟩ := d.collisionScaledJet_uniform_bound (Nat.succ_pos n) j
  refine ⟨C, hC, ?_⟩
  intro s hs hs0 hs1 q
  by_cases hq : ‖s • q‖ < delta
  · rw [collisionScaledLocal, ite_eq_left hq]
    have hprincipal (i : Fin (n + 1)) : |s * flatConstrainedAngles q i| ≤ Real.pi := by
      have hflat : flatConstrainedAngles (s • q) = fun i => s * flatConstrainedAngles q i :=
        flatConstrainedAngles_mul q s
      have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      calc
        |s * flatConstrainedAngles q i| = ‖flatConstrainedAngles (s • q) i‖ := by
          rw [hflat, Real.norm_eq_abs]
        _ ≤ ‖flatConstrainedAngles (s • q)‖ := norm_le_pi_norm _ _
        _ ≤ ((n : ℝ) + 1) * ‖s • q‖ := flatConstrainedAngles_norm_le _
        _ ≤ ((n : ℝ) + 1) * delta := mul_le_mul_of_nonneg_left hq.le hN.le
        _ ≤ Real.pi := by
          have hh := (le_div_iff₀ hN).mp hd
          nlinarith
    simpa only [collisionRationalMajorant, mul_div_assoc] using
      hbound s hs hs0 hs1 (flatConstrainedAngles q) hprincipal
  · rw [collisionScaledLocal, ite_eq_right hq, norm_zero]
    exact mul_nonneg hC.le (collisionRationalMajorant_nonneg _ _ _)

include d in
/-- All scaled actual complete jets converge under the original
independent-coordinate integral.  The only remaining amplitude task is
evaluation of the displayed genuine rational Vandermonde integral. -/
theorem collisionScaledLocal_integral_limit {n : ℕ} (j : ℕ)
    (hb : |b| < 1) (ha : 0 < (a 0).im)
    (hres : upperEdgeRoot (b : ℂ) ^ (n + 1) = 1) {delta : ℝ}
    (hd : 0 < delta) (hdpi : delta ≤ Real.pi / ((n : ℝ) + 1))
    (hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1)) :
    Tendsto (fun s : ℝ => ∫ q : Fin n → ℝ, collisionScaledLocal b a j delta s q)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ q : Fin n → ℝ, collisionLeadingJet b a j (flatConstrainedAngles q))) := by
  obtain ⟨C, _, hbound⟩ := d.collisionScaledLocal_bound j hdpi
  have hsquare : ContinuousAt (fun s : ℝ => s ^ 2) 0 := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), s ^ 2 < min d.eps0 1 :=
    hsquare.eventually (gt_mem_nhds (by simpa using lt_min d.eps0_pos zero_lt_one))
  have hsmall' := hsmall.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun q => C * collisionRationalMajorant n (j + 1) q)
  · filter_upwards [self_mem_nhdsWithin, hsmall'] with s hs he
    exact (d.collisionScaledLocal_measurable j delta hs (he.le.trans (min_le_left _ _))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hsmall'] with s hs he
    exact Filter.Eventually.of_forall (hbound s hs (he.le.trans (min_le_left _ _))
      (he.le.trans (min_le_right _ _)))
  · exact (collisionRationalMajorant_integrable hbudget).const_mul C
  · exact Filter.Eventually.of_forall fun q =>
      collisionScaledLocal_limit d.numerator hb ha hres hd q j

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
