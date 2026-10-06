import IsingBulk.Analysis.BranchEndpoint
import IsingBulk.Analysis.JetsRegularKernel

/-! Negative-coordinate attenuation controls the actual full Z product,
including all other branch coordinates, before the absolute sign split. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators

theorem allBranchExterior_one_sub_exp_neg_lower (x : ℝ) :
    x*Real.exp (-x) ≤ 1-Real.exp (-x) := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  nlinarith

theorem allBranchExterior_Z_attenuation {N : ℕ} (φ : Fin N → ℂ)
    (hi : ∀ i, (φ i).im ≤ 0) (v : Fin N) :
    1-Real.exp ((φ v).im) ≤ ‖1-regularZProduct 0 φ‖ := by
  have hsum : (∑ i, (φ i).im) ≤ (φ v).im := by
    have hh := Finset.sum_nonpos (s := Finset.univ.erase v) (fun i _ => hi i)
    have he := Finset.sum_erase_add Finset.univ (fun i => (φ i).im) (Finset.mem_univ v)
    linarith
  have hnorm : ‖regularZProduct 0 φ‖=Real.exp (∑ i, (φ i).im) := by
    rw [regularZProduct,Complex.norm_exp]
    congr 1
    simp [Complex.mul_re,Complex.im_sum]
  have hh := norm_sub_norm_le (1:ℂ) (regularZProduct 0 φ)
  rw [norm_one,hnorm] at hh
  exact (sub_le_sub_left (Real.exp_le_exp.mpr hsum) 1).trans hh

theorem allBranchExterior_negative_Z_bound {d : LocalBranchData} (B : BranchEstimates d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ B.ε₀ →
      ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ B.r) → ∀ v : Fin N, u v ≤ 0 →
      let Z := regularZProduct (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))
      c*Real.sqrt (|u v|+ε) ≤ ‖1-Z‖ ∧
      ‖deriv (originalPhase d ε) (u v)‖/‖1-Z‖ ≤ C/(|u v|+ε) := by
  let c := B.attenuationLower*Real.exp (-B.attenuationLower*Real.sqrt (2*B.r))
  have hc : 0 < c := mul_pos B.attenuationLower_pos (Real.exp_pos _)
  refine ⟨c,B.magnitudeUpper/c,hc,div_pos B.magnitudeUpper_pos hc,?_⟩
  intro N ε hε hεr u hu v hv
  dsimp only
  let φ := fun i => originalPhase d ε (u i)
  have hphi : ∀ i, (φ i).im ≤ 0 := by
    intro i
    obtain ⟨hre,him⟩ := B.quadrant ε (u i) hε hεr (hu i)
    exact (lowerArccos_sheet _ hre him).2.2.2.le
  have hL : 0 < |u v|+ε := by positivity
  have hLr : |u v|+ε ≤ 2*B.r := by linarith [hu v,B.ε₀_le_r]
  have hat := B.attenuation ε (u v) hε hεr hv (hu v)
  have hkernel := allBranchExterior_Z_attenuation φ hphi v
  have hgap : c*Real.sqrt (|u v|+ε) ≤
      ‖1-regularZProduct (radialParameter d.theta ε) φ‖ := by
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
    change 1-Real.exp ((φ v).im) ≤ ‖1-regularZProduct (radialParameter d.theta ε) φ‖ at hkernel
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
end IsingBulk.Tail
