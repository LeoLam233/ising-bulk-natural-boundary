import IsingBulk.Joint.Geometry.Definitions
import IsingBulk.Joint.RegularEdges.ComplexPolydisk
import IsingBulk.Anisotropic.Final.AnalyticInverse

/-! # Nonramified transverse curves in the independent coupling space

Every curve keeps its actual varying complex anisotropy. The inverse-function
construction is performed on its edge coordinate, never on a fixed-ratio slice.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Positive endpoint normal coordinate at free phase `b`. -/
def positiveParameter (b : ℂ) (K : Coupling) : ℂ := transferC K - transferB K - b

def curveB (curve : ℂ → Coupling) (u : ℂ) : ℂ := transferB (curve u)
def curveS (curve : ℂ → Coupling) (u : ℂ) : ℂ := S (curve u)

theorem curveS_analyticAt {curve : ℂ → Coupling} {u : ℂ}
    (hc : AnalyticAt ℂ curve u) : AnalyticAt ℂ (curveS curve) u :=
  Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)

theorem curveB_analyticAt {curve : ℂ → Coupling} {u : ℂ}
    (hc : AnalyticAt ℂ curve u) (hS : S (curve u) ≠ 0) :
    AnalyticAt ℂ (curveB curve) u :=
  (Complex.analyticAt_sinh.comp (analyticAt_snd.comp hc)).div (curveS_analyticAt hc) hS

theorem positiveParameter_analyticAt {curve : ℂ → Coupling} {u : ℂ}
    (b : ℂ) (hc : AnalyticAt ℂ curve u) (hS : S (curve u) ≠ 0) :
    AnalyticAt ℂ (fun v => positiveParameter b (curve v)) u := by
  have hA : AnalyticAt ℂ (fun v => A (curve v)) u :=
    (Complex.analyticAt_cosh.comp (analyticAt_fst.comp hc)).mul
      (Complex.analyticAt_cosh.comp (analyticAt_snd.comp hc))
  exact ((hA.div (curveS_analyticAt hc) hS).sub (curveB_analyticAt hc hS)).sub analyticAt_const

/-- Exact dispersion identity on a normalized transverse curve. -/
theorem positive_dispersion_identity (b : ℝ) (curve : ℂ → Coupling) (u q : ℂ)
    (he : positiveParameter b (curve u) = u) :
    transferC (curve u) - transferB (curve u) * Complex.cos q =
      (b:ℂ) + u + curveB curve u * (1 - Complex.cos q) := by
  dsimp [positiveParameter] at he
  dsimp [curveB]
  linear_combination he

/-- A scalar nonramified edge coordinate has an actual analytic local inverse.
Both inverse identities are retained for later transport of local extensions. -/
theorem exists_nonramified_inverse {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hfz : f z = 0) (hd : deriv f z ≠ 0) :
    ∃ psi : ℂ → ℂ, AnalyticAt ℂ psi 0 ∧ psi 0 = z ∧
      (∀ᶠ u in 𝓝 (0:ℂ), f (psi u) = u) ∧
      (∀ᶠ w in 𝓝 z, psi (f w) = w) := by
  let i := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f z) hd)
  have hfd : HasStrictFDerivAt f (i : ℂ →L[ℂ] ℂ) z :=
    hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  let e := hfd.toOpenPartialHomeomorph f
  have hz : z ∈ e.source := hfd.mem_toOpenPartialHomeomorph_source
  have he : (e : ℂ → ℂ) = f := rfl
  have hpsi : AnalyticAt ℂ e.symm (f z) := by
    rw [← he]
    exact e.analyticAt_symm' hz (by simpa only [he] using hf)
      (by simpa only [he] using hfd.hasFDerivAt.fderiv)
  refine ⟨e.symm,by simpa only [hfz] using hpsi,?_,?_,?_⟩
  · simpa only [he,hfz] using e.left_inv hz
  · have ht := e.open_target.mem_nhds (e.map_source hz)
    rw [he,hfz] at ht
    filter_upwards [ht] with u hu
    exact e.right_inv hu
  · filter_upwards [e.open_source.mem_nhds hz] with w hw
    exact e.left_inv hw

/-- Every nonramified holomorphic transverse curve admits the positive-edge
normal form with its own holomorphic, generally nonconstant `B(u)`. -/
theorem normalize_positive_curve {curve : ℂ → Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hS : S (curve z) ≠ 0)
    (he : positiveParameter b (curve z) = 0)
    (hd : deriv (fun t => positiveParameter b (curve t)) z ≠ 0) :
    ∃ psi : ℂ → ℂ, ∃ normalized : ℂ → Coupling,
      AnalyticAt ℂ psi 0 ∧ psi 0 = z ∧
      normalized = curve ∘ psi ∧ AnalyticAt ℂ normalized 0 ∧ normalized 0 = curve z ∧
      AnalyticAt ℂ (curveB normalized) 0 ∧
      (∀ᶠ u in 𝓝 (0:ℂ), positiveParameter b (normalized u) = u) ∧
      (∀ᶠ t in 𝓝 z, psi (positiveParameter b (curve t)) = t) := by
  obtain ⟨psi,hpa,hp0,hpr,hpl⟩ := exists_nonramified_inverse
    (positiveParameter_analyticAt b hc hS) he hd
  have hca : AnalyticAt ℂ (curve ∘ psi) 0 := hc.comp_of_eq hpa hp0
  refine ⟨psi,curve ∘ psi,hpa,hp0,rfl,hca,?_,?_,hpr,hpl⟩
  · simp [hp0]
  · exact curveB_analyticAt hca (by simpa [hp0] using hS)

/-- The positive side determines the genuine inside-root branch for every real
angle; no condition fixing the derivative of `B` is used. -/
theorem dispersion_im_pos {b : ℝ} {u B : ℂ} (hu : 0 < u.im) (hB : 0 < B.im) (q : ℝ) :
    0 < (RegularEdges.dispersion b (u,B) q).im := by
  simp only [RegularEdges.dispersion,Complex.add_im,Complex.ofReal_im,zero_add,
    Complex.mul_im,Complex.sub_re,Complex.one_re,Complex.ofReal_re,
    Complex.sub_im,Complex.one_im,sub_zero,mul_zero,zero_add]
  have hcos := Real.cos_le_one q
  nlinarith

end
end IsingBulk.Joint.Transverse
