import IsingBulk.Tail.AllBranchExteriorPhaseDivision

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Filter
open scoped Topology ContDiff

def allBranchSelectedPowerRatio (v θ : ℝ) (P m : ℕ) (z : (ℝ × ℝ) × ℂ) : ℂ :=
  ((z.1.1-z.1.2:ℝ):ℂ)^P/(allBranchPairPhaseDifference v θ z)^m

theorem allBranchExterior_selected_power_germ (v θ u : ℝ) (s : ℂ) (P m : ℕ) (hPm : m < P)
    (C : (ℝ × ℝ) × ℂ → ℂ) (hC : ContDiffAt ℝ ∞ C ((u,u),s)) (hCn : C ((u,u),s) ≠ 0)
    (he : ∀ᶠ y in 𝓝 ((u,u),s), allBranchPairPhaseDifference v θ y=(y.1.1-y.1.2:ℝ) • C y) :
    allBranchSelectedPowerRatio v θ P m =ᶠ[𝓝 ((u,u),s)]
      (fun y => ((y.1.1-y.1.2:ℝ):ℂ)^(P-m)/(C y)^m) := by
  have hn := hC.continuousAt.eventually_ne hCn
  filter_upwards [he,hn] with y hy hCy
  unfold allBranchSelectedPowerRatio
  rw [hy]
  change ((y.1.1-y.1.2:ℝ):ℂ)^P/(((y.1.1-y.1.2:ℝ):ℂ)*C y)^m=_
  by_cases hδ : y.1.1-y.1.2=0
  · simp [hδ,show P ≠ 0 by omega,show P-m ≠ 0 by omega]
  · have hδc : ((y.1.1-y.1.2:ℝ):ℂ) ≠ 0 := by exact_mod_cast hδ
    rw [mul_pow]
    have hp : P=(P-m)+m := by omega
    conv_lhs => rw [hp,pow_add]
    field_simp

theorem allBranchExterior_selected_power_smooth (v θ u : ℝ) (s : ℂ) (P m : ℕ) (hPm : m < P)
    (hs : s ≠ 0) (hr : 0 < (chartW s v θ (u:ℂ)).re) (hi : 0 < (chartW s v θ (u:ℂ)).im)
    (hg : angularG v θ (u:ℂ) ≠ 0) (hsi : Complex.sin (chartPhase s v θ (u:ℂ)) ≠ 0) :
    ContDiffAt ℝ ∞ (allBranchSelectedPowerRatio v θ P m) ((u,u),s) := by
  obtain ⟨C,hC,hCn,he⟩ := allBranchExterior_phase_division_nonzero v θ u s hs hr hi hg hsi
  have hδ : ContDiff ℝ ∞ (fun y : (ℝ × ℝ) × ℂ => ((y.1.1-y.1.2:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst))
  have hh : ContDiffAt ℝ ∞ (fun y => ((y.1.1-y.1.2:ℝ):ℂ)^(P-m)/(C y)^m) ((u,u),s) :=
    by
      convert! (hδ.contDiffAt.pow (P-m)).mul ((hC.pow m).inv (pow_ne_zero m hCn)) using 1
  exact hh.congr_of_eventuallyEq (allBranchExterior_selected_power_germ v θ u s P m hPm C hC hCn he)

theorem allBranchExterior_difference_power_flat (u : ℝ) (s : ℂ) (P : ℕ) (hP : 2 ≤ P)
    (G : (ℝ × ℝ) × ℂ → ℂ) (hG : DifferentiableAt ℝ G ((u,u),s)) :
    HasFDerivAt (fun y : (ℝ × ℝ) × ℂ => ((y.1.1-y.1.2:ℝ):ℂ)^P*G y) (0 : ((ℝ × ℝ) × ℂ) →L[ℝ] ℂ) ((u,u),s) := by
  let δ : (ℝ × ℝ) × ℂ → ℂ := fun y => ((y.1.1-y.1.2:ℝ):ℂ)
  have hδ : ContDiff ℝ ∞ δ :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst))
  have hp := (hδ.differentiable (by simp) ((u,u),s)).hasFDerivAt.pow P
  have hd0 : (P • δ ((u,u),s)^(P-1)) • fderiv ℝ δ ((u,u),s) = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change (P • δ ((u,u),s)^(P-1))*fderiv ℝ δ ((u,u),s) x=0
    simp [δ,show P-1≠0 by omega]
  rw [hd0] at hp
  have hh := hp.mul hG.hasFDerivAt
  have hz0 : δ ((u,u),s)^P • fderiv ℝ G ((u,u),s)+G ((u,u),s) • (0 : ((ℝ × ℝ) × ℂ) →L[ℝ] ℂ)=0 := by
    apply ContinuousLinearMap.ext
    intro x
    change δ ((u,u),s)^P*fderiv ℝ G ((u,u),s) x+G ((u,u),s)*0=0
    simp [δ,show P≠0 by omega]
  rw [hz0] at hh
  convert! hh using 1

theorem allBranchExterior_selected_power_flat (v θ u : ℝ) (s : ℂ) (P m : ℕ) (hPm : m+2 ≤ P)
    (hs : s ≠ 0) (hr : 0 < (chartW s v θ (u:ℂ)).re) (hi : 0 < (chartW s v θ (u:ℂ)).im)
    (hg : angularG v θ (u:ℂ) ≠ 0) (hsi : Complex.sin (chartPhase s v θ (u:ℂ)) ≠ 0) :
    HasFDerivAt (allBranchSelectedPowerRatio v θ P m) (0 : ((ℝ × ℝ) × ℂ) →L[ℝ] ℂ) ((u,u),s) := by
  obtain ⟨C,hC,hCn,he⟩ := allBranchExterior_phase_division_nonzero v θ u s hs hr hi hg hsi
  have hG : DifferentiableAt ℝ (fun y => ((C y)^m)⁻¹) ((u,u),s) :=
    ((hC.pow m).inv (pow_ne_zero m hCn)).differentiableAt (by simp)
  have hh := allBranchExterior_difference_power_flat u s (P-m) (by omega)
    (fun y => ((C y)^m)⁻¹) hG
  apply hh.congr_of_eventuallyEq
  have heq := allBranchExterior_selected_power_germ v θ u s P m (by omega) C hC hCn he
  simpa only [div_eq_mul_inv] using heq

end
end IsingBulk.Tail
