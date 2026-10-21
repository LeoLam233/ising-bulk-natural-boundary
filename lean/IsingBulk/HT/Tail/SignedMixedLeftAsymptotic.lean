import IsingBulk.HT.Tail.SignedMixedSectorAsymptotic
import IsingBulk.HT.Contour.SignedLeftAsymptotic
import IsingBulk.Tail.MixedLeftAsymptotic

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Contour Set Filter Asymptotics
open scoped Topology

/-- A single source selector and inner width for all separated mixed and
left sectors, all orders up to the requested finite order, and the actual
small-current interval. The full particle sum is negligible. -/
theorem signed_mixed_left_sector_sum_littleO (ξ : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (k : ℕ) (β : ℝ),k≤order → 0<β →
      radialSeriesSmall (fun eps N => signedMixedLeftSectorNorm (Complex.exp (Complex.I*(ξ:ℂ))) N (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi k (radialParameter d.theta eps) (eps^β)) := by
  obtain ⟨ηM,hηM,hM⟩ := signed_original_mixed_sector_sum_littleO ξ d hcsmall
  obtain ⟨ηL,hηL,hL⟩ := signed_original_left_compact_sector_sum_littleO ξ d hcsmall
  obtain ⟨ηCM,hηCM,hCM⟩ := signed_current_mixed_sector_sum_littleO ξ d hcsmall
  obtain ⟨ηCL,hηCL,hCL⟩ := signed_current_left_compact_sector_sum_littleO ξ d hcsmall
  refine ⟨min ηM (min ηL (min ηCM ηCL)),lt_min hηM (lt_min hηL (lt_min hηCM hηCL)),?_⟩
  intro η hη hηlt
  obtain ⟨αM,hαM,hM⟩ := hM η hη (hηlt.trans_le (min_le_left _ _))
  obtain ⟨αL,hαL,hL⟩ := hL η hη (hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨αCM,hαCM,hCM⟩ := hCM η hη
    (hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  obtain ⟨αCL,τCL,hαCL,hτCL,hCL⟩ := hCL η hη
    (hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨min αM (min αL (min αCM αCL)),lt_min hαM (lt_min hαL (lt_min hαCM hαCL)),?_⟩
  intro α hα hαlt
  have hαM' := hαlt.trans_le (min_le_left _ _)
  have hαL' := hαlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hαCM' := hαlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hαCL' := hαlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨τCM,hτCM,hCM⟩ := hCM α hα hαCM'
  refine ⟨min τCM τCL,lt_min hτCM hτCL,?_⟩
  intro τ hτ hτlt order outer cap ho hcap
  obtain ⟨iM,hiM,hiMcap,hM⟩ := hM α hα hαM' order outer cap ho hcap
  obtain ⟨iL,hiL,_hiLcap,hL⟩ := hL α hα hαL' order outer cap ho hcap
  obtain ⟨iCM,hiCM,_hiCMcap,hCM⟩ := hCM τ hτ (hτlt.trans_le (min_le_left _ _)) order outer cap ho hcap
  obtain ⟨iCL,hiCL,_hiCLcap,hCL⟩ := hCL α τ hα hαCL' hτ (hτlt.trans_le (min_le_right _ _)) order outer cap ho hcap
  refine ⟨min iM (min iL (min iCM iCL)),lt_min hiM (lt_min hiL (lt_min hiCM hiCL)),
    (min_le_left _ _).trans hiMcap,?_⟩
  intro inner hi hinner k β hk hβ
  have hM' := hM inner hi (hinner.trans (min_le_left _ _)) τ k hτ.le hk
  have hL' := hL inner hi (hinner.trans ((min_le_right _ _).trans (min_le_left _ _))) τ k hτ.le hk
  have hCM' := hCM inner hi
    (hinner.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) k β hk hβ
  have hCL' := hCL inner hi
    (hinner.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) k β hk hβ
  exact ((radialSeriesSmall.add hM' hL').add hCM').add hCL'

end
end IsingBulk.HT.Tail
