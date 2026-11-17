import IsingBulk.AnisoF002.C03.RegularOutsideMiddleTail
import IsingBulk.AnisoF002.C03.NegativeCutoffCompleteExtraction

/-!
# Constructed complete physical particle tails below any fixed cutoff

This theorem starts with the actual analytic physical data and the
reduced rational phase.  It constructs one common cutoff and one
extraction family, keeps the exact full Taylor identity, and bounds all
resonant residues outside the unchanged finite middle window.  No
analytic remainder or coefficient-identification hypothesis is added.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology BigOperators Classical

theorem exists_actual_complete_particle_tail_data {b B : ℂ → ℂ} {φ epsilon : ℝ}
    {a p : ℕ} (hepsilon : 0 < epsilon)
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hp : Odd p) (hcop : a.Coprime p) (hrat : φ = 2 * Real.pi * a / p) :
    ∃ r s Mi ki A : ℝ, ∃ hs : 0 < s,
      0 < r ∧ s ≤ epsilon ∧ 0 < Mi ∧ 0 < ki ∧ 0 < A ∧
      ∃ D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki,
        (∀ j n : ℕ, physicalOddTaylorCoefficient b B φ j n = completeCyclePoleCoefficient D j n +
          iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 / (j.factorial : ℂ)) ∧
        (∀ j : ℕ,
          Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
            (j.factorial : ℂ)‖) ∧
          Summable (fun n : ℕ => iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
            (j.factorial : ℂ)) ∧
          (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
            (j.factorial : ℂ)‖) ≤ Real.exp (completeAnalyticExponent A j)) ∧
        (∀ j : ℕ,
          Summable (fun n : ℕ => ‖completeCyclePoleCoefficient D j n‖) ∧
          Summable (completeCyclePoleCoefficient D j) ∧
          ‖completeBoundaryAnalyticRemainder D hs.le j‖ ≤ Real.exp (completeAnalyticExponent A j) ∧
          (∑' n : ℕ, physicalOddTaylorCoefficient b B φ j n) =
            (∑' n : ℕ, completeCyclePoleCoefficient D j n) + completeBoundaryAnalyticRemainder D hs.le j) ∧
        ∀ᶠ j : ℕ in atTop,
          Summable (fun q : ℕ => ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ)
            else innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖) ∧
          (∑' q : ℕ, ‖if q ∈ resonantMiddleIndices p j then (0 : ℂ)
            else innerCyclePoleCoefficient (D (resonantOddIndex p q)) j‖) ≤
            Real.exp (completeLowExponent A j) + Real.exp (completeAnalyticExponent A j) +
              Real.exp (completeHighExponent A j) := by
  obtain ⟨s0, hs0, hout⟩ := exists_actual_outside_middle_residue_bound hb hB hφ hπ hBi hbsq
  have hperiod : Complex.exp (-((p : ℂ) * ((φ : ℂ) * Complex.I))) = 1 := by
    rw [hrat]
    exact (rational_negative_phase_resonance_iff hp.pos.ne' hcop p).mpr (dvd_refl p)
  obtain ⟨r, s, Mi, ki, ar, Mr, kr, Ar, hs, hr, hscut, hMi, hki, _, _, _, hAr,
      D, _, hcoeff, _, _, hrem⟩ :=
    exists_complete_actual_analytic_remainder_below_cutoff (lt_min hepsilon hs0)
      hb hB hφ hπ hBi hbsq hp.pos hperiod
  have hs0' : s ≤ s0 := hscut.trans (min_le_right _ _)
  have hrem' (j : ℕ) :
      Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
        (j.factorial : ℂ)‖) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
        (j.factorial : ℂ)‖) ≤ Real.exp (completeAnalyticExponent Ar j) :=
    ⟨(hrem j).1, (hrem j).2.2⟩
  obtain ⟨Ao, hAo, htail⟩ := hout r s Mi ki Ar hr hs hMi.le hs0' D hs.le hcoeff hrem'
  let A := max Ar Ao
  have hA : 0 < A := hAr.trans_le (le_max_left _ _)
  have hremA (j : ℕ) :
      Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
        (j.factorial : ℂ)‖) ∧
      Summable (fun n : ℕ => iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
        (j.factorial : ℂ)) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
        (j.factorial : ℂ)‖) ≤ Real.exp (completeAnalyticExponent A j) :=
    ⟨(hrem j).1, (hrem j).2.1, ((hrem j).2.2).trans
      (Real.exp_le_exp.mpr (completeAnalyticExponent_mono (le_max_left Ar Ao) j))⟩
  refine ⟨r, s, Mi, ki, A, hs, hr, hscut.trans (min_le_left _ _), hMi, hki, hA,
    D, hcoeff, hremA, ?_, ?_⟩
  · intro j
    obtain ⟨hNs, hCs, hbnd, hsum, _⟩ := complete_boundary_extraction_of_coefficient_identities
      hb hB hφ hπ hBi hbsq D hs.le hcoeff hremA j
    exact ⟨hNs, hCs, hbnd, hsum⟩
  · filter_upwards [htail a p hp hcop hrat] with j hj
    refine ⟨hj.1, hj.2.trans ?_⟩
    exact add_le_add
      (add_le_add
        (Real.exp_le_exp.mpr (completeLowExponent_mono (le_max_right Ar Ao) j))
        (Real.exp_le_exp.mpr (completeAnalyticExponent_mono (le_max_right Ar Ao) j)))
      (Real.exp_le_exp.mpr (completeHighExponent_mono (le_max_right Ar Ao) j))

end
end IsingBulk.AnisoF002.NegativeHT
