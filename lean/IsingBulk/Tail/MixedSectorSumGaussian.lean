import IsingBulk.Tail.MixedSectorNorm
import IsingBulk.Tail.MixedOriginalSectorGaussian
import IsingBulk.Tail.MixedCurrentSectorGaussian

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology

theorem original_mixed_sector_sum_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ C : ℝ,0<C ∧ ∀ᶠ H : ℝ in atTop,∀ (n k : ℕ) (τ : ℝ),k≤order → 0≤τ →
      originalMixedSectorNorm (n+1) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*Real.exp (-H))) τ d.thetaB outer inner ho hi k
        (radialParameter d.theta (Real.exp (-H)))≤
      C^(n+1)*((n+1:ℕ):ℝ)^(5*order+2)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*(H+1)^2 := by
  obtain ⟨η₀,hη₀,hBound⟩ := mixed_original_sector_gaussian_bound d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,κ,hα₀,hκ,hBound⟩ := hBound η hη hηlt
  refine ⟨α₀,κ,hα₀,hκ,?_⟩
  intro α hα hαlt order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hBound⟩ := hBound α hα hαlt order outer (min cap (outer/4)) ho
    (lt_min hcap (by positivity))
  refine ⟨inner₀,hi₀,hicap.trans (min_le_left _ _),?_⟩
  intro inner hi hinner
  have hio : inner≤outer/4 := hinner.trans (hicap.trans (min_le_right _ _))
  obtain ⟨C,hC,hBound⟩ := hBound inner hi hinner
  refine ⟨12*C,by positivity,?_⟩
  filter_upwards [hBound] with H hBound
  intro n k τ hk hτ
  have hh := originalMixedSectorNorm_le (constructedSelector d.thetaB η α)
    (Real.exp (-d.c₀*Real.exp (-H))) τ d.thetaB outer inner ho hi hio k
    (radialParameter d.theta (Real.exp (-H))) (by positivity)
    (fun j q sigma hj hq => hBound n k τ j q sigma hk hτ hj hq)
  exact hh.trans_eq (by simp only [mul_pow]; ring)

theorem current_mixed_sector_sum_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ t C : ℝ,0<t ∧ 0<C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (n k : ℕ) (cut : ℝ),k≤order → cut∈Icc (0:ℝ) 1 → cut*τ<t →
      integratedMixedSectorNorm (n+1) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*Real.exp (-H))) τ d.thetaB outer inner ho hi k
        (radialParameter d.theta (Real.exp (-H))) cut≤
      C^(n+1)*((n+1:ℕ):ℝ)^(5*order+2)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*(H+1)^2 := by
  obtain ⟨η₀,hη₀,hBound⟩ := mixed_current_sector_gaussian_bound d hcsmall
  refine ⟨min η₀ (Real.sin d.thetaB/4),lt_min hη₀ (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨iZ,hiZ,hZero⟩ := constructed_current_named_branch_zero d.thetaB_pos d.thetaB_lt hη hηsmall
  obtain ⟨α₀,hα₀,hBound⟩ := hBound η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min α₀ (Real.sin d.thetaB/4),lt_min hα₀ (by positivity [d.a_pos]),?_⟩
  intro α hα hαlt
  have hαsmall := hαlt.trans_le (min_le_right _ _)
  obtain ⟨τ₀,hτ₀,hBound⟩ := hBound α hα (hαlt.trans_le (min_le_left _ _))
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτlt
  obtain ⟨κ,hκ,hBound⟩ := hBound τ hτ hτlt
  refine ⟨κ,hκ,?_⟩
  intro order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hBound⟩ := hBound order outer (min cap iZ) ho (lt_min hcap hiZ)
  refine ⟨inner₀,hi₀,hicap.trans (min_le_left _ _),?_⟩
  intro inner hi hinner
  obtain ⟨t,C,ht,hC,hBound⟩ := hBound inner hi hinner
  refine ⟨t,24*C,ht,by positivity,?_⟩
  filter_upwards [hBound] with H hBound
  intro n k cut hk hcut htcut
  have hh := integratedMixedSectorNorm_le (constructedSelector d.thetaB η α)
    (Real.exp (-d.c₀*Real.exp (-H))) τ d.thetaB outer inner ho hi k
    (radialParameter d.theta (Real.exp (-H))) hcut (by positivity)
    (fun q qA sigma hq lam _ => hZero inner hi (hinner.trans (hicap.trans (min_le_right _ _)))
      α hα hαsmall (n+1) q qA sigma _ τ lam outer ho hq)
    (fun j q qA sigma hj hq lam hl => hBound n k lam j q qA sigma hk hl.1
      (hl.2.trans hcut.2) ((mul_le_mul_of_nonneg_right hl.2 hτ.le).trans_lt htcut) hj hq)
  exact hh.trans_eq (by simp only [mul_pow]; ring)

end
end IsingBulk.Tail
