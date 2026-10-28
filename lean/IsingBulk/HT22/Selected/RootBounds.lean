import IsingBulk.HT22.Selected.RelativeInverse
import IsingBulk.Preferred22.SelectedRelativeDisk

namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22

 theorem selected_angular_root_bound {N : ℕ} (hN : 0<N) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ) (hτ1 : τ≤1)
    (θ : Fin N → ℝ) (i : Fin N) :
    ‖Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)‖≤Real.exp 1 := by
  have hwim := (preferred_deformedAngles_im_bound hN d B hτ θ i).trans hτ1
  have hwre : (Complex.I*deformedAngles τ B.p B.m θ i).re=
      -(deformedAngles τ B.p B.m θ i).im := by simp [Complex.mul_re]
  rw [Complex.norm_exp,hwre]
  exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hwim).1])

 theorem selected_inverse_root_disk (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ c K ρ : ℝ, 0<c ∧ 0<K ∧ 0<ρ ∧ ρ≤1 ∧
      ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ρ → 0<τ → τ<ρ →
      ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ, ‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ^2/(N:ℝ)^3 →
      ∀ i, preferredSelectedContinuedRoot d (cappedCanonicalPreferredBump d cap hcap) ε τ θ i t≠0 ∧
        ‖(preferredSelectedContinuedRoot d (cappedCanonicalPreferredBump d cap hcap) ε τ θ i t)⁻¹‖≤K := by
  obtain ⟨c,ρ,hc,hρ,hρ1,hrelative⟩ := preferred_selected_root_relative_disk d hcap
    (by norm_num : (0:ℝ)<1/2)
  let R := 3+Real.exp 1
  let K := 2*(2*R+1)
  have hK : 0<K := by dsimp [K,R]; positivity
  refine ⟨c,K,ρ,hc,hK,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw t ht i
  let B := cappedCanonicalPreferredBump d cap hcap
  let W := preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)
  have hτ1 : τ≤1 := hτρ.le.trans hρ1
  have hε1 : ε≤1 := hερ.le.trans hρ1
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hWnorm : ‖W‖≤R :=
    (norm_sub_le _ _).trans (add_le_add (preferredRadialTrace_norm_bound d hε.le hε1)
      (preferred_cos_norm_le_exp_one ((preferred_deformedAngles_im_bound hN d B hτ.le θ i).trans hτ1)))
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hoff : OffRealSegment W := Or.inl (ne_of_gt
    ((mul_pos hε hsin).trans_le (preferredActualW_im_lower d B hε.le hτ.le θ i)))
  have hinv := preferred_physical_root_inverse_bound hoff hWnorm
  have hrel := (hrelative N hN ε τ hε hερ hτ hτρ θ hw t ht i).2
  have hsmall : (1/2:ℝ)*τ/(N:ℝ)^2≤1/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    nlinarith [one_le_pow₀ hn1 (n:=2)]
  exact inverse_norm_of_relative (physicalRoot_ne_zero W) hinv (hrel.trans hsmall)

end
end IsingBulk.HT22.Selected
