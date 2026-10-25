import IsingBulk.Joint.Geometry.Definitions
import IsingBulk.Anisotropic.NegativeNormalForm.Dispersion
import IsingBulk.Anisotropic.RegularEdges.LocalParticleRoot

/-!
# The actual negative-edge coordinate on independent complex couplings

These are identities for arbitrary holomorphic curves in the two-dimensional
coupling space. In particular, `curveB` is not replaced by its value at zero.
The negative-edge local parameter is JOINT (5.8), not an ANISO temperature.
-/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm

/-- The coordinate `t=(C+B-b)/B` at a negative endpoint. -/
def edgeParameter (b : ℂ) (K : Coupling) : ℂ :=
  (transferC K + transferB K - b) / transferB K

/-- The actual, generally nonconstant anisotropy of a transverse curve. -/
def curveB (curve : ℂ → Coupling) (t : ℂ) : ℂ := transferB (curve t)

/-- The lower-root physical side, JOINT (5.8). -/
def physicalSide (B : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {t | ‖t‖ < r ∧ 0 < (B t * t).im}

theorem curveB_analyticAt {curve : ℂ → Coupling} {t : ℂ}
    (hc : AnalyticAt ℂ curve t) (hS : S (curve t) ≠ 0) :
    AnalyticAt ℂ (curveB curve) t := by
  have hs : AnalyticAt ℂ (fun u => S (curve u)) t :=
    Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)
  have ht : AnalyticAt ℂ (fun u => T (curve u)) t :=
    Complex.analyticAt_sinh.comp (analyticAt_snd.comp hc)
  exact ht.div hs hS

theorem transferB_ne_zero_of_im_neg {K : Coupling}
    (hB : (transferB K).im < 0) : transferB K ≠ 0 := by
  intro hz
  simp only [hz, Complex.zero_im, lt_self_iff_false] at hB

theorem edgeParameter_identity (b : ℂ) (K : Coupling)
    (hB : transferB K ≠ 0) :
    transferC K + transferB K = b + transferB K * edgeParameter b K := by
  dsimp [edgeParameter]
  field_simp
  ring

/-- The shifted physical dispersion agrees exactly with the variable-B model.
No derivative of the anisotropy has been discarded. -/
theorem curve_dispersion_identity (b : ℂ) (curve : ℂ → Coupling) (t delta : ℂ)
    (hB : transferB (curve t) ≠ 0) (ht : edgeParameter b (curve t) = t) :
    transferC (curve t) + transferB (curve t) * Complex.cos delta =
      negativeDispersion (curveB curve) b t delta := by
  have he := edgeParameter_identity b (curve t) hB
  rw [ht] at he
  dsimp [negativeDispersion, curveB]
  linear_combination he

/-- On the physical side every real-angle dispersion has positive imaginary
part, including the endpoint angle. This is the actual strict branch selection. -/
theorem negativeDispersion_im_pos {B : ℂ → ℂ} {b : ℝ} {t : ℂ} {delta : ℝ}
    (hB : (B t).im < 0) (ht : 0 < (B t * t).im) :
    0 < (negativeDispersion B (b : ℂ) t (delta : ℂ)).im := by
  rw [negativeDispersion, ← Complex.ofReal_cos]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
    Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
    Complex.sub_im, Complex.one_im, sub_zero, add_zero]
  have hc := Real.cos_le_one delta
  have hp : (B t * t).im = (B t).re * t.im + (B t).im * t.re := rfl
  nlinarith

/-- The inward negative ray lies in the actual curved side on one fixed disk. -/
theorem inward_ray_eventually_mem {B : ℂ → ℂ} (hB : ContinuousAt B 0)
    (hB0 : (B 0).im < 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ epsilon : ℝ in 𝓝[>] 0, -(epsilon : ℂ) ∈ physicalSide B r := by
  have hc : Tendsto (fun epsilon : ℝ => -(epsilon : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun epsilon : ℝ => -(epsilon : ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero, neg_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hsign : ∀ᶠ t : ℂ in 𝓝 0, (B t).im < 0 :=
    (Complex.continuous_im.continuousAt.comp hB).eventually_lt continuousAt_const hB0
  filter_upwards [hc.eventually hsign, hc.eventually (ball_mem_nhds (0 : ℂ) hr),
    self_mem_nhdsWithin] with epsilon hsign hnorm hpos
  refine ⟨by simpa only [mem_ball, dist_zero_right] using hnorm, ?_⟩
  simp only [Complex.mul_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
    mul_zero, Complex.neg_re, Complex.ofReal_re, zero_add]
  exact mul_pos_of_neg_of_neg hsign (neg_neg_of_pos hpos)

/-- The branch root is constructed, rather than supplied as a continuation
premise. This statement applies to every independent-coupling curve. -/
theorem curveB_has_local_square_root {curve : ℂ → Coupling}
    (hc : AnalyticAt ℂ curve 0) (hS : S (curve 0) ≠ 0)
    (hB : (transferB (curve 0)).im < 0) :
    ∃ root : ℂ → ℂ, AnalyticAt ℂ root 0 ∧ root 0 ≠ 0 ∧
      ∀ t : ℂ, root t ^ 2 = curveB curve t := by
  have hb := curveB_analyticAt hc hS
  have hn : curveB curve 0 ≠ 0 := transferB_ne_zero_of_im_neg hB
  exact ⟨IsingBulk.Anisotropic.RegularEdges.localParticleRoot (curveB curve),
    IsingBulk.Anisotropic.RegularEdges.localParticleRoot_analyticAt hb hn,
    IsingBulk.Anisotropic.RegularEdges.localParticleRoot_ne_zero hn,
    IsingBulk.Anisotropic.RegularEdges.localParticleRoot_sq hn⟩

end
end IsingBulk.Joint.Negative
