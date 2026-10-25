import IsingBulk.Joint.FormFactors.ComplexRatioFamilies
import IsingBulk.Joint.FormFactors.NormalConvergence

/-! Compact admissible actual complex-ratio families and uniform bounds for
all their fixed mixed complex jets. No constant is chosen separately for each
real ratio; the whole complex parameter polydisk is compacted at once. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology

namespace ComplexRatioFamily
variable {edge amp : Coupling → ℂ} {sign : ℝ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily edge amp sign z₀ lam₀)

def polydisk : Set Coupling := closedBall (0:ℂ) F.radius ×ˢ closedBall lam₀ F.radius

def anisotropy (q : Coupling) : ℂ := transferB (F.coupling q)
def scale (q : Coupling) : ℂ := S (F.coupling q)
def amplitude (q : Coupling) : ℂ := amp (F.coupling q)

def parameterSet : Set (ℂ × ℂ) := (fun q => (F.anisotropy q,F.scale q)) '' F.polydisk

theorem polydisk_isCompact : IsCompact F.polydisk :=
  (isCompact_closedBall (0:ℂ) F.radius).prod (isCompact_closedBall lam₀ F.radius)

theorem polydisk_bounds {q : Coupling} (hq : q∈F.polydisk) :
    ‖q.1‖≤2*F.radius ∧ ‖q.2-lam₀‖≤2*F.radius := by
  have h1 : ‖q.1‖≤F.radius := by simpa only [mem_closedBall,dist_zero_right] using hq.1
  have h2 : ‖q.2-lam₀‖≤F.radius := by simpa only [mem_closedBall,dist_eq_norm] using hq.2
  constructor <;> linarith [F.radius_pos]

theorem anisotropy_analyticOnNhd : AnalyticOnNhd ℂ F.anisotropy F.polydisk := by
  intro q hq
  exact F.anisotropy_analytic q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2

theorem scale_analyticOnNhd : AnalyticOnNhd ℂ F.scale F.polydisk := by
  intro q hq
  exact F.scale_analytic q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2

theorem amplitude_analyticOnNhd : AnalyticOnNhd ℂ F.amplitude F.polydisk := by
  intro q hq
  exact F.prefactor_analytic q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2

include F in
theorem central_sign_pos : 0<sign*(transferB (z₀,lam₀*z₀)).im := by
  have hh := F.anisotropy_margin 0 lam₀ (by simp only [norm_zero]; linarith [F.radius_pos])
    (by simp only [sub_self,norm_zero]; linarith [F.radius_pos])
  rw [F.coupling_zero] at hh
  linarith

theorem anisotropy_sign {q : Coupling} (hq : q∈F.polydisk) : 0<sign*(F.anisotropy q).im := by
  have hh := F.anisotropy_margin q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2
  exact (half_pos F.central_sign_pos).trans hh

theorem anisotropy_ne_zero {q : Coupling} (hq : q∈F.polydisk) : F.anisotropy q≠0 := by
  intro hz
  have hh := F.anisotropy_sign hq
  simp only [hz,Complex.zero_im,mul_zero,lt_self_iff_false] at hh

theorem scale_ne_zero {q : Coupling} (hq : q∈F.polydisk) : F.scale q≠0 := by
  apply norm_pos_iff.mp
  have hh := F.scale_margin q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2
  exact (div_nonneg (norm_nonneg _) (by norm_num : (0:ℝ)≤2)).trans_lt hh

theorem amplitude_ne_zero {q : Coupling} (hq : q∈F.polydisk) : F.amplitude q≠0 := by
  apply norm_pos_iff.mp
  have hh := F.prefactor_margin q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2
  exact (div_nonneg (norm_nonneg _) (by norm_num : (0:ℝ)≤2)).trans_lt hh

/-- This single compact image supplies the independent-parameter all-particle
bounds, including parameters varying over both complex disks simultaneously. -/
theorem parameterSet_isCompact : IsCompact F.parameterSet :=
  F.polydisk_isCompact.image_of_continuousOn
    (F.anisotropy_analyticOnNhd.continuousOn.prodMk F.scale_analyticOnNhd.continuousOn)

theorem parameterSet_sign {v : ℂ × ℂ} (hv : v∈F.parameterSet) : 0<sign*v.1.im := by
  obtain ⟨q,hq,rfl⟩ := hv
  exact F.anisotropy_sign hq

theorem parameterSet_scale_ne_zero {v : ℂ × ℂ} (hv : v∈F.parameterSet) : v.2≠0 := by
  obtain ⟨q,hq,rfl⟩ := hv
  exact F.scale_ne_zero hq

theorem zero_mem_polydisk {lam : ℂ} (hl : lam∈closedBall lam₀ F.radius) :
    ((0:ℂ),lam)∈F.polydisk := ⟨mem_closedBall_self F.radius_pos.le,hl⟩

/-- Exact hypotheses for the negative compact-family normal-form API, with
E=complex lambda and with no frozen anisotropy. -/
theorem central_anisotropy_analytic {lam : ℂ} (hl : lam∈closedBall lam₀ F.radius) :
    AnalyticAt ℂ F.anisotropy (0,lam) := F.anisotropy_analyticOnNhd _ (F.zero_mem_polydisk hl)

theorem central_anisotropy_ne_zero {lam : ℂ} (hl : lam∈closedBall lam₀ F.radius) :
    F.anisotropy (0,lam)≠0 := F.anisotropy_ne_zero (F.zero_mem_polydisk hl)

end ComplexRatioFamily

/-- Compactness is applied to the actual jointly analytic derivatives, on one
common complex polydisk with a larger analytic collar. -/
theorem compact_analytic_all_jets_bound {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] {f : Coupling → G} {K : Set Coupling}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) (j : ℕ) :
    ∃ M : ℝ, 0<M ∧ ∀ q∈K, ‖iteratedFDeriv ℂ j f q‖≤M := by
  have hc : ContinuousOn (iteratedFDeriv ℂ j f) K := by
    intro q hq
    have hh : ContDiffAt ℂ j f q := (hf q hq).contDiffAt
    exact (hh.continuousAt_iteratedFDeriv le_rfl).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨max M 0+1,by linarith [le_max_right M 0],fun q hq =>
    (hM q hq).trans (by linarith [le_max_left M 0])⟩

namespace ComplexRatioFamily
variable {edge amp : Coupling → ℂ} {sign : ℝ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily edge amp sign z₀ lam₀)

/-- Every fixed mixed derivative has a uniform bound over ALL complex ratios
and edge parameters in the same compact polydisk. -/
theorem all_mixed_jets_bound (j : ℕ) :
    ∃ M : ℝ, 0<M ∧ ∀ q∈F.polydisk,
      ‖iteratedFDeriv ℂ j F.anisotropy q‖≤M ∧
      ‖iteratedFDeriv ℂ j F.scale q‖≤M ∧ ‖iteratedFDeriv ℂ j F.amplitude q‖≤M := by
  obtain ⟨M₁,hM₁,hb⟩ := compact_analytic_all_jets_bound F.polydisk_isCompact F.anisotropy_analyticOnNhd j
  obtain ⟨M₂,hM₂,hs⟩ := compact_analytic_all_jets_bound F.polydisk_isCompact F.scale_analyticOnNhd j
  obtain ⟨M₃,hM₃,ha⟩ := compact_analytic_all_jets_bound F.polydisk_isCompact F.amplitude_analyticOnNhd j
  refine ⟨M₁+M₂+M₃,by positivity,fun q hq => ?_⟩
  exact ⟨(hb q hq).trans (by linarith),(hs q hq).trans (by linarith),(ha q hq).trans (by linarith)⟩

end ComplexRatioFamily

/-- Interior holomorphy genuinely includes complex-ratio neighborhoods of
lambda=1. No noncollinearity hypothesis is imposed on interior points. -/
theorem high_bulk_complexRatio_contDiffAt (j : ℕ) {q : Coupling}
    (hq : complexRatioMap q∈highDomain) :
    ContDiffAt ℂ j (highNormalizedBulk ∘ complexRatioMap) q :=
  (highNormalizedBulk_contDiffAt j hq).comp q (complexRatioMap_analyticAt q).contDiffAt

theorem low_bulk_complexRatio_contDiffAt (j : ℕ) {q : Coupling}
    (hq : complexRatioMap q∈lowDomain) :
    ContDiffAt ℂ j (lowNormalizedBulk ∘ complexRatioMap) q :=
  (lowNormalizedBulk_contDiffAt j hq).comp q (complexRatioMap_analyticAt q).contDiffAt

end
end IsingBulk.Joint.FormFactors
