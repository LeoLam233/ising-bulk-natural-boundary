import IsingBulk.AnisoF002.NegativeHT.RadialBetaTail
import IsingBulk.AnisoF002.C03.NegativeTailLogAbsorption

/-!
# The integrated beta tail for every sufficiently large integer order

Integer floors absorb the full exponential perturbation without restricting
the Taylor orders to a congruence class.  The exact beta ratio and full
physical particle exponent are retained.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open MeasureTheory Set

theorem absorbed_exponential_majorant {k : ℕ} (hk : 8 ≤ k) {x E : ℝ}
    (hx : 0 ≤ x) (hE : E ≤ (k : ℝ) / 8 * Real.log (1 + x)) :
    Real.exp E / (1 + x) ^ k ≤ 1 / (1 + x) ^ (k / 2 + k / 4 + 1) := by
  have hp : 0 < 1 + x := by linarith
  have hlog : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hdeg : 8 * (k / 2 + k / 4 + 1) ≤ 7 * k := by omega
  have hdegR : 8 * ((k / 2 + k / 4 + 1 : ℕ) : ℝ) ≤ 7 * (k : ℝ) := by
    exact_mod_cast hdeg
  have hdeg' : ((k / 2 + k / 4 + 1 : ℕ) : ℝ) ≤ 7 * (k : ℝ) / 8 := by linarith
  have hexp : E + ((k / 2 + k / 4 + 1 : ℕ) : ℝ) * Real.log (1 + x) ≤
      (k : ℝ) * Real.log (1 + x) := by
    have hh := mul_le_mul_of_nonneg_right hdeg' hlog
    nlinarith
  have hpow (j : ℕ) : Real.exp ((j : ℝ) * Real.log (1 + x)) = (1 + x) ^ j := by
    rw [Real.exp_nat_mul, Real.exp_log hp]
  apply (div_le_div_iff₀ (pow_pos hp _) (pow_pos hp _)).mpr
  rw [one_mul, ← hpow, ← hpow, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp

set_option maxHeartbeats 1000000 in
theorem arbitrary_order_radial_tail_gaussian (n k : ℕ)
    (hn : 2 ≤ n) (hk : 64 * n ^ 2 ≤ k) :
    (∫ x in Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ)),
      radialBetaDensity (particleExponent n) (k / 2 + k / 4) x) /
        radialBeta (particleExponent n) (k - 1) ≤ Real.exp (-(n : ℝ) ^ 2 / 4) := by
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hk0 : 0 < k := by omega
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hα0 : 0 < particleExponent n := by unfold particleExponent; omega
  have hαhi : 2 * particleExponent n ≤ n ^ 2 := by unfold particleExponent; omega
  have hαlo : n ^ 2 ≤ 4 * particleExponent n := by unfold particleExponent; omega
  have hαhiR : 2 * (particleExponent n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hαhi
  have hαloR : (n : ℝ) ^ 2 ≤ 4 * (particleExponent n : ℝ) := by exact_mod_cast hαlo
  have hK : k ≤ 8 * (k / 4) := by omega
  have hKR : (k : ℝ) ≤ 8 * ((k / 4 : ℕ) : ℝ) := by exact_mod_cast hK
  have hcut : 0 ≤ 32 * (n : ℝ) ^ 2 / (k : ℝ) := by positivity
  have hcut1 : 32 * (n : ℝ) ^ 2 / (k : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hkR).mpr
    have hh : 64 * (n : ℝ) ^ 2 ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [sq_nonneg (n : ℝ)]
  have hlarge : 8 * (particleExponent n : ℝ) ≤
      ((k / 4 : ℕ) : ℝ) * (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hkR).mpr
    have hh := mul_le_mul_of_nonneg_right hKR (by positivity : 0 ≤ 4 * (n : ℝ) ^ 2)
    have ha := mul_le_mul_of_nonneg_right hαhiR (by positivity : 0 ≤ 4 * (k : ℝ))
    nlinarith
  have he := normalized_radialBeta_tail_exp (particleExponent n) (k / 2) (k - 1) (k / 4)
    hα0 (by omega) (by omega) (by omega) hcut hcut1 hlarge
  exact he.trans (Real.exp_le_exp.mpr (by linarith))

theorem absorbed_beta_tail_integral (n k : ℕ) (hn : 2 ≤ n) (hk : 64 * n ^ 2 ≤ k)
    {E : ℝ → ℝ}
    (hE : ∀ x ∈ Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ)),
      E x ≤ (k : ℝ) / 8 * Real.log (1 + x))
    (hEmeas : AEStronglyMeasurable (fun x => x ^ (particleExponent n - 1) * Real.exp (E x) /
      (1 + x) ^ k) (volume.restrict (Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ))))) :
    IntegrableOn (fun x => x ^ (particleExponent n - 1) * Real.exp (E x) / (1 + x) ^ k)
      (Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ))) ∧
    (∫ x in Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ)),
      x ^ (particleExponent n - 1) * Real.exp (E x) / (1 + x) ^ k) /
        radialBeta (particleExponent n) (k - 1) ≤ Real.exp (-(n : ℝ) ^ 2 / 4) := by
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hk8 : 8 ≤ k := by omega
  have hα0 : 0 < particleExponent n := by unfold particleExponent; omega
  have hαk : particleExponent n ≤ k / 2 + k / 4 := by
    have hh := particleExponent_le_sq n
    omega
  have hcut : 0 ≤ 32 * (n : ℝ) ^ 2 / (k : ℝ) := by positivity
  have hsub : Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ)) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hcut
  have hi := (integrableOn_radialBetaDensity (particleExponent n) (k / 2 + k / 4) hα0 hαk).mono_set hsub
  have hb : ∀ x ∈ Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ)),
      0 ≤ x ^ (particleExponent n - 1) * Real.exp (E x) / (1 + x) ^ k ∧
      x ^ (particleExponent n - 1) * Real.exp (E x) / (1 + x) ^ k ≤
        radialBetaDensity (particleExponent n) (k / 2 + k / 4) x := by
    intro x hx
    have hx0 : 0 ≤ x := (hsub hx).le
    refine ⟨by positivity, ?_⟩
    have hh := mul_le_mul_of_nonneg_left (absorbed_exponential_majorant hk8 hx0 (hE x hx))
      (pow_nonneg hx0 (particleExponent n - 1))
    simpa only [radialBetaDensity, div_eq_mul_inv, one_mul, mul_assoc] using hh
  have hf : IntegrableOn (fun x => x ^ (particleExponent n - 1) * Real.exp (E x) / (1 + x) ^ k)
      (Ioi (32 * (n : ℝ) ^ 2 / (k : ℝ))) := by
    apply hi.mono' hEmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (hb x hx).1]
    exact (hb x hx).2
  refine ⟨hf, ?_⟩
  have hh := integral_mono_ae hf hi
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using (hb x hx).2)
  exact (div_le_div_of_nonneg_right hh
    (radialBeta_pos (particleExponent n) (k - 1) hα0 (by
      have hh := particleExponent_le_sq n; omega)).le).trans
      (arbitrary_order_radial_tail_gaussian n k hn hk)

end
end IsingBulk.AnisoF002.NegativeHT
