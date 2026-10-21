import IsingBulk.HT.Contour.SignedLeftSectorGaussian
import IsingBulk.HT.Contour.SignedLeftSectorNorm
import IsingBulk.Tail.MixedRadialAsymptotic

/-! Full all-particle original and actual small-current left-compact signed
sector series, negligible on the inverse-square-root radial scale. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Tail Set Filter Asymptotics
open scoped Topology

theorem signed_original_left_compact_sector_sum_littleO (ξ : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (τ : ℝ) (k : ℕ),0≤τ → k≤order →
      let E := fun eps N => signedOriginalLeftCompactSectorNorm (Complex.exp (Complex.I*(ξ:ℂ))) N (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi k (radialParameter d.theta eps)
      (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
        (fun eps : ℝ => ∑' N,E eps N) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨η₀,hη₀,hBound⟩ := signed_left_compact_original_sector_gaussian_bound ξ d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,κ,hα₀,hκ,hBound⟩ := hBound η hη hηlt
  refine ⟨α₀,hα₀,?_⟩
  intro α hα hαlt order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hBound⟩ := hBound α hα hαlt order outer cap ho hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner τ k hτ hk
  obtain ⟨C,hC,hBound⟩ := hBound inner hi hinner
  apply mixed_atTop_gaussian_littleO _ (C := 12*C) (κ := κ) (4*order+2) (by positivity) hκ
    (fun eps N => signedOriginalLeftCompactSectorNorm_nonneg (Complex.exp (Complex.I*(ξ:ℂ))) N _ _ _ _ _ _ _ _ _ _)
    (fun eps => signedOriginalLeftCompactSectorNorm_zero (Complex.exp (Complex.I*(ξ:ℂ))) _ _ _ _ _ _ _ _ _ _)
  filter_upwards [hBound] with H hh
  intro n
  have hb := signedOriginalLeftCompactSectorNorm_le (Complex.exp (Complex.I*(ξ:ℂ))) (constructedSelector d.thetaB η α)
    (Real.exp (-d.c₀*Real.exp (-H))) τ d.thetaB outer inner ho hi k
    (radialParameter d.theta (Real.exp (-H))) (by positivity)
    (fun a q sigma ha hn => hh (n+1) k τ a q sigma (by omega) hk hτ ha hn)
  exact hb.trans_eq (by simp only [mul_pow]; ring)

theorem signed_current_left_compact_sector_sum_littleO (ξ : ℝ) (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ,0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,0<α → α<α₀ → 0<τ → τ<τ₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (k : ℕ) (β : ℝ),k≤order → 0<β →
      let E := fun eps N => signedIntegratedLeftCompactSectorNorm (Complex.exp (Complex.I*(ξ:ℂ))) N (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi k (radialParameter d.theta eps) (eps^β)
      (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
        (fun eps : ℝ => ∑' N,E eps N) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨η₀,hη₀,hBound⟩ := signed_left_compact_current_sector_gaussian_bound ξ d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hBound⟩ := hBound η hη hηlt
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  obtain ⟨κ,hκ,hBound⟩ := hBound α τ hα hαlt hτ hτlt
  intro order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hBound⟩ := hBound order outer cap ho hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner k β hk hβ
  obtain ⟨t,C,ht,hC,hBound⟩ := hBound inner hi hinner
  apply mixed_gaussian_log_majorant_littleO _ (C := 24*C) (κ := κ) (4*order+2) (by positivity) hκ
    (fun eps N => signedIntegratedLeftCompactSectorNorm_nonneg (Complex.exp (Complex.I*(ξ:ℂ))) N _ _ _ _ _ _ _ _ _ _ _)
  filter_upwards [log_inverse_tendsto_atTop.eventually hBound,self_mem_nhdsWithin,
    radial_power_cutoff_eventually hβ τ ht] with eps hh heps hcut
  intro N
  cases N with
  | zero => rw [signedIntegratedLeftCompactSectorNorm_zero]; positivity
  | succ n =>
    have heq : Real.exp (-Real.log (1/eps))=eps := by
      rw [one_div,Real.log_inv,neg_neg,Real.exp_log heps]
    have hb := signedIntegratedLeftCompactSectorNorm_le (Complex.exp (Complex.I*(ξ:ℂ))) (constructedSelector d.thetaB η α)
      (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi k
      (radialParameter d.theta eps)
      (Q := C^(n+1)*((n+1:ℕ):ℝ)^(4*order+2)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*(Real.log (1/eps)+1)^2)
      hcut.1 (by positivity)
      (fun a q qA sigma ha hn lam hl => by
        have hp := hh (n+1) k lam a q qA sigma (by omega) hk hl.1 (hl.2.trans hcut.1.2)
          ((mul_le_mul_of_nonneg_right hl.2 hτ.le).trans_lt hcut.2) ha hn
        simpa only [heq] using hp)
    exact hb.trans_eq (by simp only [mul_pow]; ring)

end
end IsingBulk.HT.Contour
