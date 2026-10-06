import IsingBulk.Analysis.BranchScaled
import IsingBulk.Analysis.BranchSlope

/-! The actual second-derivative sign on the source scale u >= C0*epsilon. -/
namespace IsingBulk.Branch
noncomputable section

theorem original_concavity (d : LocalBranchData) :
    ∃ c C₀ r : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < r ∧ ∀ ε u : ℝ,
      0 < ε → ε < r → C₀*ε ≤ u → u < r →
      c/(u*Real.sqrt u) ≤ -deriv (deriv (originalRealPhase d ε)) u := by
  obtain ⟨c,r₁,hc,hr₁,hnegative⟩ := scaledSecond_negative_near d
  obtain ⟨r₂,hr₂,hbranch⟩ := original_branch_inclusion d
  let C₀ := 2/r₁
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨c,C₀,min r₁ r₂,hc,hC₀,lt_min hr₁ hr₂,?_⟩
  intro ε u hε hεr hscale hur
  have hu : 0 < u := (mul_pos hC₀ hε).trans_le hscale
  have hratio : |ε/u| < r₁ := by
    rw [abs_of_pos (div_pos hε hu)]
    have hscale' : 2*ε ≤ r₁*u := by
      have h := mul_le_mul_of_nonneg_left hscale hr₁.le
      dsimp [C₀] at h
      field_simp at h
      nlinarith
    apply (div_lt_iff₀ hu).mpr
    nlinarith [mul_pos hr₁ hu]
  have hneg := hnegative u (ε/u)
    (by simpa [abs_of_pos hu] using hur.trans_le (min_le_left _ _)) hratio
  obtain ⟨hre,him⟩ := hbranch ε u hε (hεr.trans_le (min_le_right _ _))
    (by simpa [abs_of_pos hu] using hur.trans_le (min_le_right _ _))
  have hev : u*(ε/u) = ε := by field_simp
  have hidentity := scaledSecond_identity d u (ε/u) hu
    (by rw [hev]; linarith) (by simpa [hev,originalW] using hre) (by simpa [hev,originalW] using him)
  rw [hev] at hidentity
  have hi := congrArg Complex.re hidentity
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hi
  have he : originalRealPhase d ε = (fun v => (currentPhase d ε 0 v).re) := by funext v; rfl
  rw [he,realPhase_second_deriv d ε 0 u hre him]
  apply (div_le_iff₀ (mul_pos hu (Real.sqrt_pos.mpr hu))).mpr
  nlinarith

end
end IsingBulk.Branch
