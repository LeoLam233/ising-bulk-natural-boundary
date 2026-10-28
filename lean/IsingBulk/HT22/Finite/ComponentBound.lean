import IsingBulk.HT22.FullTail.PartitionBound
import IsingBulk.HT22.FullTail.EpsilonLimit
namespace IsingBulk.HT22.Finite
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Physical IsingBulk.HT22.Selected Filter
open scoped Topology ContDiff

theorem coefficient_log_bound_of_components (negative : Bool) (k : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (j : ℕ)
    (hF : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (selectedIntegral negative (2*(k+1)) τ B.p B.m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C)
    (hA : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      Anchor.derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)≤C)
    (hR : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (rightPopulationIntegral negative (2*(k+1)) τ preferredPopulationCutoff B.p B.m r)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|)) :
    ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (signedCoefficient negative (2*(k+1)+1))
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|) := by
  obtain ⟨CF,eF,hCF,heF,hF⟩ := hF
  obtain ⟨CA,eA,hCA,heA,hA⟩ := hA
  obtain ⟨CR,eR,hCR,heR,hR⟩ := hR
  refine ⟨CF+2*(CA+CR),min eF (min eA eR),by positivity,by positivity,?_⟩
  intro ε hε hεe
  have hf := hF ε hε (hεe.trans_le (min_le_left _ _))
  have ha := hA ε hε (hεe.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hright := hR ε hε (hεe.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hh := FullTail.signed_coefficient_norm_le negative k d B hτ hε r hr j
  nlinarith [abs_nonneg (Real.log ε)]

theorem complex_epsilon_zero_of_log_bound (f : ℝ → ℂ)
    (hbound : ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e → ‖f ε‖≤C*(1+|Real.log ε|)) :
    Tendsto (fun ε : ℝ => ε • f ε) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  obtain ⟨C,e,_hC,he,hb⟩ := hbound
  have hnorm := FullTail.epsilon_limit_of_log_bound (fun ε => ‖f ε‖) he
    (fun ε hε hεe => ⟨norm_nonneg _,hb ε hε hεe⟩)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hnorm.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0<ε := hε
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hε]
end
end IsingBulk.HT22.Finite
