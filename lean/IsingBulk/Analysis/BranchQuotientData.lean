import IsingBulk.Analysis.BranchConcavity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Proved local estimates for the two quotient regimes. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology
open Set

theorem original_slope_regular (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε u : ℝ, 0 < ε → ε < r → |u| < r →
      DifferentiableAt ℝ (deriv (originalRealPhase d ε)) u := by
  obtain ⟨r,hr,hbranch⟩ := original_branch_inclusion d
  refine ⟨r,hr,?_⟩
  intro ε u hε hεr hur
  obtain ⟨hre,him⟩ := hbranch ε u hε hεr hur
  have hd := currentPhase_second_hasDerivAt d ε 0 u hre him
  have hdre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd
  have he : deriv (fun v => (currentPhase d ε 0 v).re) =ᶠ[𝓝 u]
      (fun v => (deriv (currentPhase d ε 0) v).re) := by
    filter_upwards [current_phase_quadrant_near d ε 0 u hre him] with v hv
    exact realPhase_deriv d ε 0 v hv.1 hv.2
  have hf : originalRealPhase d ε = (fun v => (currentPhase d ε 0 v).re) := by funext v; rfl
  rw [hf]
  exact (hdre.congr_of_eventuallyEq he).differentiableAt

structure OriginalQuotientData (d : LocalBranchData) where
  a : ℝ
  C : ℝ
  k : ℝ
  C₀ : ℝ
  r : ℝ
  a_pos : 0 < a
  C_pos : 0 < C
  k_pos : 0 < k
  C₀_pos : 0 < C₀
  r_pos : 0 < r
  slope : ∀ ε u, 0 < ε → ε < r → 0 ≤ u → u < r →
    a/Real.sqrt (u+ε) ≤ deriv (originalRealPhase d ε) u ∧
    deriv (originalRealPhase d ε) u ≤ C/Real.sqrt (u+ε)
  magnitude : ∀ ε u, 0 < ε → ε < r → 0 ≤ u → u < r →
    ‖deriv (originalPhase d ε) u‖ ≤ C/Real.sqrt (u+ε)
  concavity : ∀ ε u, 0 < ε → ε < r → C₀*ε ≤ u → u < r →
    k/(u*Real.sqrt u) ≤ -deriv (deriv (originalRealPhase d ε)) u
  regular : ∀ ε u, 0 < ε → ε < r → 0 ≤ u → u < r →
    DifferentiableAt ℝ (deriv (originalRealPhase d ε)) u

theorem original_quotient_data (d : LocalBranchData) : Nonempty (OriginalQuotientData d) := by
  obtain ⟨a,C₁,r₁,ha,hC₁,hr₁,hslope⟩ := original_positive_slope d
  obtain ⟨_,C₂,r₂,_,hC₂,hr₂,hmag⟩ := original_derivative_magnitude d
  obtain ⟨k,C₀,r₃,hk,hC₀,hr₃,hconcave⟩ := original_concavity d
  obtain ⟨r₄,hr₄,hregular⟩ := original_slope_regular d
  let r := min r₁ (min r₂ (min r₃ r₄))
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₃ : r ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrr₄ : r ≤ r₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨⟨a,max C₁ C₂,k,C₀,r,ha,lt_of_lt_of_le hC₁ (le_max_left _ _),hk,hC₀,
    lt_min hr₁ (lt_min hr₂ (lt_min hr₃ hr₄)),?_,?_,?_,?_⟩⟩
  · intro ε u hε hεr hu hur
    obtain ⟨hl,hu'⟩ := hslope ε u hε (hεr.trans_le hrr₁) hu (hur.trans_le hrr₁)
    exact ⟨hl,hu'.trans (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))⟩
  · intro ε u hε hεr hu hur
    have h := (hmag ε u hε (hεr.trans_le hrr₂) (by simpa [abs_of_nonneg hu] using hur.trans_le hrr₂)).2
    simp only [abs_of_nonneg hu] at h
    exact h.trans (div_le_div_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
  · intro ε u hε hεr hscale hur
    exact hconcave ε u hε (hεr.trans_le hrr₃) hscale (hur.trans_le hrr₃)
  · intro ε u hε hεr hu hur
    exact hregular ε u hε (hεr.trans_le hrr₄) (by simpa [abs_of_nonneg hu] using hur.trans_le hrr₄)

theorem OriginalQuotientData.slope_drop {d : LocalBranchData} (B : OriginalQuotientData d)
    (ε m M : ℝ) (hε : 0 < ε) (hεr : ε < B.r) (hscale : B.C₀*ε ≤ m)
    (hmM : m < M) (hMr : M < B.r) :
    B.k*(M-m)/(M*Real.sqrt M) ≤
      deriv (originalRealPhase d ε) m-deriv (originalRealPhase d ε) M := by
  have hm : 0 < m := (mul_pos B.C₀_pos hε).trans_le hscale
  have hM : 0 < M := hm.trans hmM
  let f := deriv (originalRealPhase d ε)
  have hc : ContinuousOn f (Icc m M) := by
    intro u hu
    exact (B.regular ε u hε hεr (hm.le.trans hu.1) (hu.2.trans_lt hMr)).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ f (Ioo m M) := by
    intro u hu
    exact (B.regular ε u hε hεr (hm.le.trans hu.1.le) (hu.2.trans hMr)).differentiableWithinAt
  obtain ⟨u,hu,he⟩ := exists_deriv_eq_slope f hmM hc hd
  have hup : 0 < u := hm.trans hu.1
  have hb := B.concavity ε u hε hεr (hscale.trans hu.1.le) (hu.2.trans hMr)
  have hcomp : B.k/(M*Real.sqrt M) ≤ B.k/(u*Real.sqrt u) :=
    div_le_div₀ B.k_pos.le le_rfl (mul_pos hup (Real.sqrt_pos.mpr hup))
      (mul_le_mul hu.2.le (Real.sqrt_le_sqrt hu.2.le) (Real.sqrt_nonneg _) hM.le)
  have hdrop : B.k/(M*Real.sqrt M) ≤ -(f M-f m)/(M-m) := by rw [neg_div,← he]; exact hcomp.trans hb
  have hv := (le_div_iff₀ (sub_pos.mpr hmM)).mp hdrop
  dsimp [f] at hv
  calc
    _ = (B.k/(M*Real.sqrt M))*(M-m) := by ring
    _ ≤ _ := by linarith

end
end IsingBulk.Branch
