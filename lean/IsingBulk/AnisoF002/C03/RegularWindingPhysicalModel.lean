import IsingBulk.AnisoF002.C03.RegularWindingFirstUniform
import IsingBulk.AnisoF002.C03.NegativeUniformAllCutoffs

/-!
# The literal physical first-winding pair versus the exact frozen model

The two real-cycle sectors, with their actual cutoff and original measure,
are attached to the constructed residue estimate.  The physical-root sign
is exactly +sqrt(B(0))/b(0), as forced by the checked Taylor/residue identity.
All constants and the maximal cutoff are chosen before particle number.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

theorem exists_physical_first_pair_model_comparison {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ s0 M E : ℝ, 0 < s0 ∧ 0 < M ∧ 0 < E ∧
      ∀ s : ℝ, 0 < s → s ≤ s0 → ∀ r Mi ki : ℝ, ∀ᶠ l : ℕ in atTop,
        ∀ d : InnerRemainderFamily b B φ (2 * l + 1) r s Mi ki, ∀ j : ℕ,
          M * (((2 * l + 1 : ℕ) : ℝ)) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) →
          Real.log (j : ℝ) ≤ ((2 * l + 1 : ℕ) : ℝ) →
          let model := modelCoefficient (2 * l + 1) j (B (windingTau (2 * l + 1) : ℂ))
            (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
              (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))
          ‖physicalWindingSectorCoefficient d j 1 + physicalWindingSectorCoefficient d j (-1) -
              (Complex.sqrt (B 0) / b 0) * model‖ ≤
            E * (((2 * l + 1 : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)) * ‖model‖ := by
  obtain ⟨σ, C, Kρ, Kp, M, E, hσ, _, hC, _, _, _, hM, hE, hmodel⟩ :=
    exists_uniform_physical_first_winding_comparison_all_cutoffs hb hB hφ hπ hBi hbsq
  obtain ⟨sa, hsa, hatt⟩ := exists_uniform_first_winding_sector_attachment hB hφ hπ hBi
  let s0 := min sa (σ ^ 2 / 4)
  have hs0 : 0 < s0 := lt_min hsa (by positivity)
  refine ⟨s0, M, E, hs0, hM, hE, ?_⟩
  intro s hs hss0 r Mi ki
  have hssa : s ≤ sa := hss0.trans (min_le_left _ _)
  have hsσ : s < σ ^ 2 := (hss0.trans (min_le_right _ _)).trans_lt (by nlinarith)
  have ht : Tendsto (fun l : ℕ => 2 * l) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    exact eventually_atTop.mpr ⟨k, fun l hl => by omega⟩
  have ha := ht.eventually (hatt σ C Kρ Kp s hσ hC.le hs hssa hsσ b r Mi ki)
  have hm := hmodel (Real.sqrt (s / 2)) (Real.sqrt_pos.mpr (half_pos hs))
  filter_upwards [ha, hm] with l hla hlm
  intro d j hj hlog
  obtain ⟨p, hp⟩ := hlm
  obtain ⟨hRlo, hRhi, he⟩ := hla d p
  have hh := (hp j (firstWindingCutRadius (2 * l) s) hj hlog hRlo hRhi).2
  dsimp only at hh ⊢
  rw [(he j).2.2]
  exact hh

end
end IsingBulk.AnisoF002.NegativeHT
