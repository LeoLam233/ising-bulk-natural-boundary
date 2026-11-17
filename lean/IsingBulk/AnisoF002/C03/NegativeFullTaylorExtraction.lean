import IsingBulk.AnisoF002.C03.NegativeCompleteAnalyticRemainder

/-!
# Full physical boundary jets equal all resonant residues plus the small remainder

The limit is the normalized derivative of the complete physical odd
series.  The infinite residue sum and the complete analytic remainder
are separately absolutely convergent at every order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical BigOperators

def completeBoundaryAnalyticRemainder {b B : ℂ → ℂ} {φ r s Mi ki : ℝ}
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki) (hs : 0 ≤ s)
    (j : ℕ) : ℂ :=
  ∑' n : ℕ, iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ)

theorem complete_boundary_extraction_of_coefficient_identities {b B : ℂ → ℂ}
    {φ r s Mi ki A : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki) (hs : 0 ≤ s)
    (hcoeff : ∀ j n : ℕ, physicalOddTaylorCoefficient b B φ j n = completeCyclePoleCoefficient D j n +
      iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ))
    (hrem : ∀ j : ℕ,
      Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
        (j.factorial : ℂ)‖) ∧
      Summable (fun n : ℕ => iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
        (j.factorial : ℂ)) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 /
        (j.factorial : ℂ)‖) ≤
        Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * j + A)) :
    ∀ j : ℕ,
      Summable (fun n : ℕ => ‖completeCyclePoleCoefficient D j n‖) ∧
      Summable (completeCyclePoleCoefficient D j) ∧
      ‖completeBoundaryAnalyticRemainder D hs j‖ ≤
        Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * j + A) ∧
      (∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n) =
        (∑' n : ℕ, completeCyclePoleCoefficient D j n) + completeBoundaryAnalyticRemainder D hs j ∧
      Tendsto (fun eps : ℝ => iteratedDeriv j (negativePhysicalOddSum b B φ) (-(eps : ℂ)) /
          (j.factorial : ℂ)) (𝓝[>] 0)
        (𝓝 ((∑' n : ℕ, completeCyclePoleCoefficient D j n) + completeBoundaryAnalyticRemainder D hs j)) := by
  intro j
  obtain ⟨hphys, hlimit⟩ := physical_oddSum_boundary_jets hb hB hφ hπ hBi hbsq j
  have hphysN : Summable (fun n : ℕ => ‖physicalOddTaylorCoefficient b B φ j n‖) := by
    simpa only [physicalOddTaylorCoefficient, norm_div, norm_natCast] using
      hphys.div_const (j.factorial : ℝ)
  have hPdiff (n : ℕ) : completeCyclePoleCoefficient D j n =
      physicalOddTaylorCoefficient b B φ j n -
        iteratedDeriv j (completeCycleAnalyticRemainder D hs n) 0 / (j.factorial : ℂ) := by
    rw [hcoeff j n]
    ring
  have hPN : Summable (fun n : ℕ => ‖completeCyclePoleCoefficient D j n‖) :=
    (hphysN.add (hrem j).1).of_norm_bounded (fun n => by
      rw [norm_norm, hPdiff n]
      exact norm_sub_le _ _)
  have hPs : Summable (completeCyclePoleCoefficient D j) := hPN.of_norm
  have hsmall : ‖completeBoundaryAnalyticRemainder D hs j‖ ≤
      Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * j + A) :=
    (norm_tsum_le_tsum_norm (hrem j).1).trans (hrem j).2.2
  have hsum : (∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n) =
      (∑' n : ℕ, completeCyclePoleCoefficient D j n) + completeBoundaryAnalyticRemainder D hs j := by
    simp_rw [hcoeff j]
    exact hPs.tsum_add (hrem j).2.1
  refine ⟨hPN, hPs, hsmall, hsum, ?_⟩
  have hlim : Tendsto (fun eps : ℝ => iteratedDeriv j (negativePhysicalOddSum b B φ) (-(eps : ℂ)) /
      (j.factorial : ℂ)) (𝓝[>] 0) (𝓝 (∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n)) := by
    simpa only [physicalOddTaylorCoefficient, tsum_div_const] using hlimit.div_const (j.factorial : ℂ)
  rwa [hsum] at hlim

theorem exists_full_actual_boundary_extraction {b B : ℂ → ℂ} {φ : ℝ} {p : ℕ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hp : 0 < p) (hperiod : Complex.exp (-((p : ℂ) * ((φ : ℂ) * Complex.I))) = 1) :
    ∃ r s Mi ki A : ℝ, ∃ hs : 0 < s,
      0 < r ∧ 0 < Mi ∧ 0 < ki ∧ 0 < A ∧
      ∃ D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki,
        (∀ j n : ℕ, physicalOddTaylorCoefficient b B φ j n = completeCyclePoleCoefficient D j n +
          iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 / (j.factorial : ℂ)) ∧
        ∀ j : ℕ,
          Summable (fun n : ℕ => ‖completeCyclePoleCoefficient D j n‖) ∧
          Summable (completeCyclePoleCoefficient D j) ∧
          ‖completeBoundaryAnalyticRemainder D hs.le j‖ ≤
            Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * j + A) ∧
          (∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n) =
            (∑' n : ℕ, completeCyclePoleCoefficient D j n) + completeBoundaryAnalyticRemainder D hs.le j ∧
          Tendsto (fun eps : ℝ => iteratedDeriv j (negativePhysicalOddSum b B φ) (-(eps : ℂ)) /
              (j.factorial : ℂ)) (𝓝[>] 0)
            (𝓝 ((∑' n : ℕ, completeCyclePoleCoefficient D j n) + completeBoundaryAnalyticRemainder D hs.le j)) := by
  obtain ⟨r, s, Mi, ki, _, _, _, A, hs, hr, hMi, hki, _, _, _, hA, D, _, hcoeff, _, _, hrem⟩ :=
    exists_complete_actual_analytic_remainder hb hB hφ hπ hBi hbsq hp hperiod
  exact ⟨r, s, Mi, ki, A, hs, hr, hMi, hki, hA, D, hcoeff,
    complete_boundary_extraction_of_coefficient_identities hb hB hφ hπ hBi hbsq D hs.le hcoeff hrem⟩

end
end IsingBulk.AnisoF002.NegativeHT
