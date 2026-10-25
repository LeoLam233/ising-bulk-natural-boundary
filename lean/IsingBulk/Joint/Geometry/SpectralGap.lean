import IsingBulk.Joint.Geometry.Basic
import Mathlib.Topology.Order.Compact

namespace IsingBulk.Joint
noncomputable section
open Set Metric

/-- The literal affine spectral polynomial, before elimination. -/
def spectralLinear (K : Coupling) (ab : ℝ × ℝ) : ℂ :=
  A K - S K * (ab.1 : ℂ) - T K * (ab.2 : ℂ)

def spectralSquare : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc (-1) 1

theorem spectralSquare_isCompact : IsCompact spectralSquare := isCompact_Icc.prod isCompact_Icc

theorem spectralSquare_nonempty : spectralSquare.Nonempty := ⟨(0,0),by norm_num [spectralSquare]⟩

@[fun_prop] theorem spectralLinear_continuous : Continuous (fun v : Coupling × (ℝ × ℝ) =>
    spectralLinear v.1 v.2) := by unfold spectralLinear; fun_prop

theorem spectral_min_exists (K : Coupling) : ∃ ab ∈ spectralSquare,
    ∀ cd ∈ spectralSquare, ‖spectralLinear K ab‖ ≤ ‖spectralLinear K cd‖ := by
  exact spectralSquare_isCompact.exists_isMinOn (f := fun ab => ‖spectralLinear K ab‖)
    spectralSquare_nonempty (by unfold spectralLinear; fun_prop)

def spectralMinimizer (K : Coupling) : ℝ × ℝ := (spectral_min_exists K).choose

theorem spectralMinimizer_mem (K : Coupling) : spectralMinimizer K ∈ spectralSquare :=
  (spectral_min_exists K).choose_spec.1

/-- The positive spectral gap in JOINT (2.24), defined by its attained minimum. -/
def spectralGap (K : Coupling) : ℝ := ‖spectralLinear K (spectralMinimizer K)‖

theorem spectralGap_nonneg (K : Coupling) : 0 ≤ spectralGap K := norm_nonneg _

theorem spectralGap_le (K : Coupling) {ab : ℝ × ℝ} (hab : ab ∈ spectralSquare) :
    spectralGap K ≤ ‖spectralLinear K ab‖ := (spectral_min_exists K).choose_spec.2 ab hab

theorem spectralGap_eq_zero_iff (K : Coupling) : spectralGap K = 0 ↔ K ∈ spectralSet := by
  constructor
  · intro h
    have he : spectralLinear K (spectralMinimizer K) = 0 := norm_eq_zero.mp h
    exact ⟨(spectralMinimizer K).1,(spectralMinimizer_mem K).1,
      (spectralMinimizer K).2,(spectralMinimizer_mem K).2,by dsimp [spectralLinear] at he; linear_combination he⟩
  · rintro ⟨a,ha,b,hb,he⟩
    have hh := spectralGap_le K (ab := (a,b)) ⟨ha,hb⟩
    have hz : spectralLinear K (a,b) = 0 := by dsimp [spectralLinear]; linear_combination he
    rw [hz,norm_zero] at hh
    exact le_antisymm hh (spectralGap_nonneg K)

theorem spectralGap_pos_iff (K : Coupling) : 0 < spectralGap K ↔ K ∉ spectralSet := by
  rw [← spectralGap_eq_zero_iff,lt_iff_le_and_ne]
  simp [spectralGap_nonneg,ne_comm]

private theorem spectralLinear_difference_bound (K L : Coupling) {ab : ℝ × ℝ}
    (hab : ab ∈ spectralSquare) :
    ‖spectralLinear K ab - spectralLinear L ab‖ ≤ ‖A K-A L‖+‖S K-S L‖+‖T K-T L‖ := by
  have h₁ : ‖(ab.1 : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr hab.1
  have h₂ : ‖(ab.2 : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr hab.2
  calc ‖spectralLinear K ab - spectralLinear L ab‖
      = ‖(A K-A L) - (S K-S L)*(ab.1 : ℂ) - (T K-T L)*(ab.2 : ℂ)‖ := by congr 1; unfold spectralLinear; ring
    _ ≤ ‖A K-A L‖ + ‖(S K-S L)*(ab.1 : ℂ)‖ + ‖(T K-T L)*(ab.2 : ℂ)‖ :=
      (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ ‖A K-A L‖ + ‖S K-S L‖ + ‖T K-T L‖ := by
      simp only [norm_mul]
      gcongr <;> exact mul_le_of_le_one_right (norm_nonneg _) (by assumption)

private theorem spectralGap_sub_le (K L : Coupling) :
    spectralGap K - spectralGap L ≤ ‖A K-A L‖+‖S K-S L‖+‖T K-T L‖ := by
  have h := spectralGap_le K (spectralMinimizer_mem L)
  have hd := (norm_sub_norm_le (spectralLinear K (spectralMinimizer L))
    (spectralLinear L (spectralMinimizer L))).trans
      (spectralLinear_difference_bound K L (spectralMinimizer_mem L))
  dsimp [spectralGap] at *
  linarith

theorem spectralGap_dist_le (K L : Coupling) :
    dist (spectralGap K) (spectralGap L) ≤ ‖A K-A L‖+‖S K-S L‖+‖T K-T L‖ := by
  rw [Real.dist_eq,abs_le]
  have h := spectralGap_sub_le L K
  rw [norm_sub_rev (A L),norm_sub_rev (S L),norm_sub_rev (T L)] at h
  exact ⟨by linarith,spectralGap_sub_le K L⟩

@[fun_prop] theorem spectralGap_continuous : Continuous spectralGap := by
  apply continuous_iff_continuousAt.mpr
  intro K
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hc : Continuous (fun L : Coupling => ‖A L-A K‖+‖S L-S K‖+‖T L-T K‖) := by fun_prop
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ,hδ,?_⟩
  intro L hL
  have he := hd hL
  simp only [sub_self,norm_zero,add_zero,dist_zero_right] at he
  exact (spectralGap_dist_le L K).trans_lt (lt_of_le_of_lt (le_abs_self _) he)

end
end IsingBulk.Joint
