import IsingBulk.Tail.AllBranchExteriorNegativeKernel
import IsingBulk.HT.Lie.SignedBranchKernel
import IsingBulk.HT.Lie.SignedKernelDensity

/-! Negative-coordinate attenuation for the actual signed collective root
product. The lower gap is phase-independent and retains every spectator. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail IsingBulk.HT.Lie
open scoped BigOperators

 theorem signed_kernel_ne_zero_of_micro {n : ℕ} (σ : ℂ) (hσ : ‖σ‖ = 1)
    (v θ : ℝ) (hv : v < 0) (s : ℂ) (u : AngularSpace n)
    (h : MicrocoreJetPoint v θ s u) :
    signedRegularKernel σ s (chartMap v θ s u) ≠ 0 := by
  have hy : ∀ i, ‖regularY s (chartMap v θ s u i)‖ < 1 := by
    intro i
    rw [show chartMap v θ s u i=chartPhase s v θ (u i) from rfl,
      regularY_chartPhase _ _ _ _ (h.g_pos i),angularY_norm_real,Real.exp_lt_one_iff]
    exact hv
  have hz : ∀ i, ‖Complex.exp (-Complex.I*chartMap v θ s u i)‖ < 1 := by
    intro i
    rw [show chartMap v θ s u i=chartPhase s v θ (u i) from rfl,← chart_root_eq_physical]
    exact interiorRoot_norm_lt_one (h.im_pos i)
  unfold signedRegularKernel
  apply mul_ne_zero
  · exact IsingBulk.HT.Contour.signed_product_gap_ne_zero (by omega) σ hσ _ hy
  · rw [regularZProduct_eq_prod]
    exact IsingBulk.HT.Contour.signed_product_gap_ne_zero (by omega) σ hσ _ hz

theorem signed_exterior_kernel_density_continuousOn {n : ℕ} (ξ : ℝ) (d : LocalBranchData)
    {ε : ℝ} (hε : 0 < ε) (S : Set (AngularSpace n))
    (hp : ∀ u ∈ S, MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) :
    ContinuousOn (signedExteriorKernelDensity (Complex.exp (Complex.I*(ξ:ℂ))) d ε) S := by
  apply signed_kernel_density_continuousOn _ d S hp
  intro u hu
  exact signed_kernel_ne_zero_of_micro _ (by simp [Complex.norm_exp,Complex.mul_re])
    (-d.c₀*ε) d.thetaB (by nlinarith [d.c₀_pos]) _ u (hp u hu)

theorem signed_exterior_Z_attenuation (σ : ℂ) (hσ : ‖σ‖ = 1) {N : ℕ} (φ : Fin N → ℂ)
    (hi : ∀ i, (φ i).im ≤ 0) (v : Fin N) :
    1-Real.exp ((φ v).im) ≤ ‖1-σ*regularZProduct 0 φ‖ := by
  have hsum : (∑ i, (φ i).im) ≤ (φ v).im := by
    have hh := Finset.sum_nonpos (s := Finset.univ.erase v) (fun i _ => hi i)
    have he := Finset.sum_erase_add Finset.univ (fun i => (φ i).im) (Finset.mem_univ v)
    linarith
  have hnorm : ‖regularZProduct 0 φ‖=Real.exp (∑ i, (φ i).im) := by
    rw [regularZProduct,Complex.norm_exp]
    congr 1
    simp [Complex.mul_re,Complex.im_sum]
  have hh := norm_sub_norm_le (1:ℂ) (σ*regularZProduct 0 φ)
  rw [norm_one,norm_mul,hσ,one_mul,hnorm] at hh
  exact (sub_le_sub_left (Real.exp_le_exp.mpr hsum) 1).trans hh

theorem signed_exterior_negative_Z_bound {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ σ : ℂ, ‖σ‖ = 1 → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ B.ε₀ →
      ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ B.r) → ∀ v : Fin N, u v ≤ 0 →
      let Z := regularZProduct (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))
      c*Real.sqrt (|u v|+ε) ≤ ‖1-σ*Z‖ ∧
      ‖deriv (originalPhase d ε) (u v)‖/‖1-σ*Z‖ ≤ C/(|u v|+ε) := by
  let c := B.attenuationLower*Real.exp (-B.attenuationLower*Real.sqrt (2*B.r))
  have hc : 0 < c := mul_pos B.attenuationLower_pos (Real.exp_pos _)
  refine ⟨c,B.magnitudeUpper/c,hc,div_pos B.magnitudeUpper_pos hc,?_⟩
  intro σ hσ N ε hε hεr u hu v hv
  dsimp only
  let φ := fun i => originalPhase d ε (u i)
  have hphi : ∀ i, (φ i).im ≤ 0 := by
    intro i
    obtain ⟨hre,him⟩ := B.quadrant ε (u i) hε hεr (hu i)
    exact (lowerArccos_sheet _ hre him).2.2.2.le
  have hL : 0 < |u v|+ε := by positivity
  have hLr : |u v|+ε ≤ 2*B.r := by linarith [hu v,B.ε₀_le_r]
  have hat := B.attenuation ε (u v) hε hεr hv (hu v)
  have hkernel := signed_exterior_Z_attenuation σ hσ φ hphi v
  have hgap : c*Real.sqrt (|u v|+ε) ≤
      ‖1-σ*regularZProduct (radialParameter d.theta ε) φ‖ := by
    have hexp : Real.exp (-B.attenuationLower*Real.sqrt (2*B.r)) ≤
        Real.exp (-(B.attenuationLower*Real.sqrt (|u v|+ε))) := by
      apply Real.exp_le_exp.mpr
      have hh := Real.sqrt_le_sqrt hLr
      nlinarith [B.attenuationLower_pos]
    have hh := allBranchExterior_one_sub_exp_neg_lower (B.attenuationLower*Real.sqrt (|u v|+ε))
    have hphiExp : Real.exp ((φ v).im) ≤ Real.exp (-(B.attenuationLower*Real.sqrt (|u v|+ε))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg B.attenuationLower_pos.le (Real.sqrt_nonneg (|u v|+ε)))
    dsimp [c] at hmul ⊢
    change 1-Real.exp ((φ v).im) ≤ ‖1-σ*regularZProduct (radialParameter d.theta ε) φ‖ at hkernel
    nlinarith
  refine ⟨hgap,?_⟩
  have hmag := (B.magnitude ε (u v) hε hεr (hu v)).2
  have hs : 0 < Real.sqrt (|u v|+ε) := Real.sqrt_pos.mpr hL
  have hbound := div_le_div₀ (div_nonneg B.magnitudeUpper_pos.le (Real.sqrt_nonneg _))
    hmag (mul_pos hc hs) hgap
  apply hbound.trans_eq
  have he := Real.sq_sqrt hL.le
  field_simp
  rw [he]

end
end IsingBulk.HT.Tail
