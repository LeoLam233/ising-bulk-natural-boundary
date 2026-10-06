import IsingBulk.Tail.UpperExteriorSeries
import IsingBulk.Tail.RightExteriorSeries
import IsingBulk.Tail.ExteriorChartGeometry
import IsingBulk.First.FarExteriorRadiusIndependence
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Actual form-factor gluing on overlapping exterior trace charts. Every
piece is a normalized source contour integral or its proved symmetry image. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter Metric
open scoped Topology BigOperators

@[simp] theorem sourceS_conj_map (s : ℂ) :
    sourceS ((starRingEnd ℂ) s) = (starRingEnd ℂ) (sourceS s) := sourceS_conjugate s

def exteriorEvenTerm (n : ℕ) (s : ℂ) : ℂ :=
  if 0 < (sourceS s).im then upperFormFactor (2*(n+1)) s
  else if (sourceS s).im < 0 then star (upperFormFactor (2*(n+1)) (star s))
  else if 2 < (sourceS s).re then rightFormFactor (2*(n+1)) s
  else rightFormFactor (2*(n+1)) (-s)

theorem rightFormFactor_conjugate (N : ℕ) (s : ℂ) :
    rightFormFactor N (star s) = star (rightFormFactor N s) := by
  have hr : rightCanonicalRadius (star s) = rightCanonicalRadius s := by
    simp [rightCanonicalRadius]
  simp only [rightFormFactor,hr,doubleFormFactor_conjugate]

theorem upperEvenTerm_neg_conjugate (n : ℕ) (s : ℂ) :
    upperFormFactor (2*(n+1)) (-star s) = star (upperFormFactor (2*(n+1)) s) := by
  have hr : canonicalRadius (-star s) = canonicalRadius s := by
    simp [canonicalRadius,sourceS_neg]
  simp only [upperFormFactor,hr,doubleFormFactor_even _ (even_two_mul (n+1)),
    doubleFormFactor_conjugate]

theorem exteriorEvenTerm_eq_upper (n : ℕ) {s : ℂ} (hs : 0 < (sourceS s).im) :
    exteriorEvenTerm n s = upperFormFactor (2*(n+1)) s := by simp [exteriorEvenTerm,hs]

theorem exteriorEvenTerm_eq_lower (n : ℕ) {s : ℂ} (hs : (sourceS s).im < 0) :
    exteriorEvenTerm n s = star (upperFormFactor (2*(n+1)) (star s)) := by
  simp [exteriorEvenTerm,hs,not_lt.mpr hs.le]

theorem exteriorEvenTerm_eq_right (n : ℕ) {s : ℂ} (hs : 2 < (sourceS s).re) :
    exteriorEvenTerm n s = rightFormFactor (2*(n+1)) s := by
  by_cases hu : 0 < (sourceS s).im
  · rw [exteriorEvenTerm_eq_upper n hu]
    exact (rightFormFactor_eq_upper _ (by omega) hs hu).symm
  · by_cases hl : (sourceS s).im < 0
    · rw [exteriorEvenTerm_eq_lower n hl]
      have hsc : 2 < (sourceS (star s)).re := by simpa [sourceS_conj_map] using hs
      have hic : 0 < (sourceS (star s)).im := by simpa [sourceS_conj_map] using neg_pos.mpr hl
      rw [← rightFormFactor_eq_upper _ (by omega) hsc hic,rightFormFactor_conjugate,star_star]
    · simp [exteriorEvenTerm,hu,hl,hs]

theorem exteriorEvenTerm_eq_left (n : ℕ) {s : ℂ} (hs : (sourceS s).re < -2) :
    exteriorEvenTerm n s = rightFormFactor (2*(n+1)) (-s) := by
  have hn : 2 < (sourceS (-s)).re := by simp only [sourceS_neg,Complex.neg_re]; linarith
  by_cases hu : 0 < (sourceS s).im
  · rw [exteriorEvenTerm_eq_upper n hu]
    have hnc : 2 < (sourceS (-star s)).re := by
      simp only [sourceS_neg,sourceS_conj_map,Complex.neg_re,Complex.star_def,Complex.conj_re]
      linarith
    have hni : 0 < (sourceS (-star s)).im := by
      simpa [sourceS_neg] using hu
    have he := rightFormFactor_eq_upper (2*(n+1)) (by omega) hnc hni
    have hstar := congrArg star he
    rw [upperEvenTerm_neg_conjugate,star_star] at hstar
    have hc : star (-s) = -star s := by simp
    rw [← hc,rightFormFactor_conjugate,star_star] at hstar
    exact hstar.symm
  · by_cases hl : (sourceS s).im < 0
    · rw [exteriorEvenTerm_eq_lower n hl]
      have hni : 0 < (sourceS (-s)).im := by simpa [sourceS_neg] using neg_pos.mpr hl
      rw [rightFormFactor_eq_upper _ (by omega) hn hni]
      simpa only [star_star] using (upperEvenTerm_neg_conjugate n (star s)).symm
    · have hnr : ¬ 2 < (sourceS s).re := by linarith
      simp [exteriorEvenTerm,hu,hl,hnr]

def exteriorDomain : Set ℂ := {s | 1 < ‖s‖}
def lowerTraceDomain : Set ℂ := {s | (sourceS s).im < 0}
def leftTraceDomain : Set ℂ := {s | (sourceS s).re < -2}

theorem exteriorDomain_isOpen : IsOpen exteriorDomain := isOpen_lt continuous_const continuous_norm

theorem lowerTraceDomain_isOpen : IsOpen lowerTraceDomain := by
  have he : lowerTraceDomain = (fun s : ℂ => star s) ⁻¹' upperTraceDomain := by
    ext s
    simp [lowerTraceDomain,upperTraceDomain]
  rw [he]
  exact upperTraceDomain_isOpen.preimage continuous_star

theorem leftTraceDomain_isOpen : IsOpen leftTraceDomain := by
  have he : leftTraceDomain = (fun s : ℂ => -s) ⁻¹' rightTraceDomain := by
    ext s
    simp only [leftTraceDomain,rightTraceDomain,mem_ofPred_eq,mem_preimage,
      sourceS_neg,Complex.neg_re]
    constructor <;> intro h <;> linarith
  rw [he]
  exact rightTraceDomain_isOpen.preimage continuous_neg

theorem analyticAt_conjugate_reflection {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f (star s)) :
    AnalyticAt ℂ (fun t => star (f (star t))) s := by
  have he : ∀ᶠ t in 𝓝 s, AnalyticAt ℂ f (star t) :=
    (continuous_star.continuousAt : ContinuousAt (fun t : ℂ => star t) s).tendsto.eventually
      hf.eventually_analyticAt
  apply DifferentiableOn.analyticAt (s := {t | AnalyticAt ℂ f (star t)}) _ he
  intro t ht
  have hh := ht.differentiableAt.star_star
  simpa only [Function.comp_def,star_star] using hh.differentiableWithinAt

theorem exteriorEvenTerm_analyticAt (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticAt ℂ (exteriorEvenTerm n) s := by
  rcases exterior_trace_charts hs with hu | hl | hr | hL
  · apply (upperFormFactor_analyticAt (2*(n+1)) (by omega) hu).congr
    filter_upwards [upperTraceDomain_isOpen.mem_nhds hu] with t ht
    exact (exteriorEvenTerm_eq_upper n ht).symm
  · have hc : 0 < (sourceS (star s)).im := by simpa [sourceS_conj_map] using neg_pos.mpr hl
    apply (analyticAt_conjugate_reflection
      (upperFormFactor_analyticAt (2*(n+1)) (by omega) hc)).congr
    filter_upwards [lowerTraceDomain_isOpen.mem_nhds hl] with t ht
    exact (exteriorEvenTerm_eq_lower n ht).symm
  · apply (rightFormFactor_analyticAt (2*(n+1)) (by omega) hr).congr
    filter_upwards [rightTraceDomain_isOpen.mem_nhds hr] with t ht
    exact (exteriorEvenTerm_eq_right n ht).symm
  · have hn : 2 < (sourceS (-s)).re := by simp only [sourceS_neg,Complex.neg_re]; linarith
    apply ((rightFormFactor_analyticAt (2*(n+1)) (by omega) hn).comp
      (analyticAt_id.neg)).congr
    filter_upwards [leftTraceDomain_isOpen.mem_nhds hL] with t ht
    exact (exteriorEvenTerm_eq_left n ht).symm

theorem upperFormFactor_eq_quarter_far (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hu : 0 < (sourceS s).im) (hs : 16 < ‖s‖) :
    upperFormFactor N s = doubleFormFactor N (1/4) s := by
  obtain ⟨hr,hr1,hm⟩ := canonicalRadius_admissible hu
  let R : ℝ := max (1/4) (canonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_right _ _)
  have hR1 : R < 1 := max_lt (by norm_num) hr1
  have hmr : R⁻¹-R < (sourceS s).im :=
    (inverse_radius_drop_mono hr (le_max_right _ _)).trans_lt hm
  rw [upperFormFactor_eq_fixed_radius N hN hR hR1 hmr]
  exact farExterior_doubleFormFactor_radius_eq N hN le_rfl hR1 (le_max_left _ _) hs

theorem rightFormFactor_eq_quarter_far (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hu : 2 < (sourceS s).re) (hs : 16 < ‖s‖) :
    rightFormFactor N s = doubleFormFactor N (1/4) s := by
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible hu
  let R : ℝ := max (1/4) (rightCanonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_right _ _)
  have hR1 : R < 1 := max_lt (by norm_num) hr1
  have hi : R⁻¹ ≤ (rightCanonicalRadius s)⁻¹ := inv_anti₀ hr (le_max_right _ _)
  have hmr : 1+R⁻¹ < (sourceS s).re := by linarith
  rw [rightFormFactor_eq_fixed_radius N hN hR hR1 hmr]
  exact farExterior_doubleFormFactor_radius_eq N hN le_rfl hR1 (le_max_left _ _) hs

/-- The globally glued actual terms agree with the verified FIRST germ near
infinity, including the real-axis charts. -/
theorem exteriorEvenTerm_eq_quarter_far (n : ℕ) {s : ℂ} (hs : 16 < ‖s‖) :
    exteriorEvenTerm n s = doubleFormFactor (2*(n+1)) (1/4) s := by
  rcases exterior_trace_charts (show 1 < ‖s‖ by linarith) with hu | hl | hr | hL
  · rw [exteriorEvenTerm_eq_upper n hu]
    exact upperFormFactor_eq_quarter_far _ (by omega) hu hs
  · have hc : 0 < (sourceS (star s)).im := by simpa using neg_pos.mpr hl
    rw [exteriorEvenTerm_eq_lower n hl,upperFormFactor_eq_quarter_far _ (by omega) hc (by simpa using hs),
      doubleFormFactor_conjugate,star_star]
  · rw [exteriorEvenTerm_eq_right n hr]
    exact rightFormFactor_eq_quarter_far _ (by omega) hr hs
  · have hn : 2 < (sourceS (-s)).re := by simp only [sourceS_neg,Complex.neg_re]; linarith
    rw [exteriorEvenTerm_eq_left n hL,rightFormFactor_eq_quarter_far _ (by omega) hn (by simpa using hs),
      doubleFormFactor_even _ (even_two_mul (n+1))]

end
end IsingBulk.Tail
