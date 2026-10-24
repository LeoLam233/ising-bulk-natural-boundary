import IsingBulk.Anisotropic.RegularEdges.EdgeNeighborhood
import IsingBulk.Tail.RootAttenuation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric
open scoped Topology

/-- The actual local dispersion has a uniformly quadratic angular imaginary margin. -/
theorem edgeParamW_im_margin (b : ℝ) {B : ℂ→ℂ} {u : ℂ} {β : ℝ}
    (hβ : 0≤β) (hB : β≤(B u).im) {q : ℝ} (hq : |q|≤Real.pi) :
    u.im+(2*β/Real.pi^2)*q^2 ≤ (edgeParamW b B u q).im := by
  have hcos := Real.cos_le_one_sub_mul_cos_sq hq
  have hm : (2*β/Real.pi^2)*q^2≤β*(1-Real.cos q) := by
    calc
      _ = β*(2/Real.pi^2*q^2) := by ring
      _ ≤ β*(1-Real.cos q) := mul_le_mul_of_nonneg_left (by linarith) hβ
  have hm' := mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr (Real.cos_le_one q))
  simp only [edgeParamW,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.sub_im,Complex.one_im]
  nlinarith

theorem edgeParamW_norm_bound (b : ℝ) {B : ℂ→ℂ} {u : ℂ} {M : ℝ}
    (hu : ‖u‖≤1) (hB : ‖B u‖≤M) (q : ℝ) :
    ‖edgeParamW b B u q‖≤|b|+1+2*M := by
  have hM : 0≤M := (norm_nonneg _).trans hB
  have hc : ‖(1:ℂ)-(Real.cos q:ℂ)‖≤2 := by
    have h := norm_sub_le (1:ℂ) (Real.cos q:ℂ)
    simp only [norm_one,Complex.norm_real,Real.norm_eq_abs] at h
    linarith [Real.abs_cos_le_one q]
  have hm := mul_le_mul hB hc (norm_nonneg _) hM
  have h1 := norm_add_le ((b:ℂ)+u) (B u*(1-(Real.cos q:ℂ)))
  have h2 := norm_add_le (b:ℂ) u
  rw [norm_mul] at h1
  simp only [Complex.norm_real,Real.norm_eq_abs] at h2
  unfold edgeParamW
  linarith

/-- Uniform root coercivity on the actual analytic sheet, for every nearby upper parameter.
No angular or order-dependent root choice is introduced. -/
theorem edgeParamRoot_uniform_gap {b : ℝ} {B : ℂ→ℂ}
    (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ u in 𝓝 (0:ℂ), ∀ q∈Icc (-Real.pi) Real.pi,
      0<u.im → c*(u.im+q^2)≤1-‖edgeParamRoot b B u q‖ := by
  let M := |b|+1+2*(‖B 0‖+1)
  let k := (B 0).im/Real.pi^2
  let d := min 1 k
  have hM : 0<M := by dsimp [M]; positivity
  have hk : 0<k := by dsimp [k]; positivity
  have hd : 0<d := lt_min (by norm_num) hk
  refine ⟨d/(2*M+1),by positivity,?_⟩
  have hBi : ∀ᶠ u in 𝓝 (0:ℂ), (B 0).im/2<(B u).im :=
    (Complex.continuous_im.continuousAt.comp hc).eventually_const_lt (by change (B 0).im/2<(B 0).im; linarith)
  have hBn : ∀ᶠ u in 𝓝 (0:ℂ), ‖B u‖<‖B 0‖+1 := hc.norm.eventually_lt_const (by linarith)
  have hun : ∀ᶠ u in 𝓝 (0:ℂ), ‖u‖<1 := continuousAt_id.norm.eventually_lt_const (by simp)
  filter_upwards [hBi,hBn,hun] with u hBi hBn hun q hq hui
  have hm := edgeParamW_im_margin b (by positivity : 0≤(B 0).im/2) hBi.le (abs_le.mpr hq)
  have hm' : u.im+k*q^2≤(edgeParamW b B u q).im := by
    dsimp [k]
    convert hm using 1; ring
  have hm'' : d*(u.im+q^2)≤(edgeParamW b B u q).im := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) k) hui.le
    have h2 := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) k) (sq_nonneg q)
    dsimp [d]
    nlinarith
  have hw : 0<(edgeParamW b B u q).im :=
    lt_of_lt_of_le (by nlinarith [mul_nonneg hk.le (sq_nonneg q)]) hm'
  have hnorm : ‖edgeParamW b B u q‖≤M := edgeParamW_norm_bound b hun.le hBn.le q
  have hgap := interiorRoot_modulus_gap hw hnorm
  have hdiv := (div_le_div_of_nonneg_right hm'' (by positivity : 0≤2*M+1)).trans hgap
  simpa only [edgeParamRoot,continuedRoot_eq_interiorRoot hw,div_mul_eq_mul_div] using hdiv

/-- Explicit inward-parameter version used by the full lattice-resolvent estimates. -/
theorem edgeParamRoot_inward_gap {b : ℝ} {B : ℂ→ℂ}
    (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ ε : ℝ, 0<ε → ε<δ → ∀ q∈Icc (-Real.pi) Real.pi,
      c*(ε+q^2)≤1-‖edgeParamRoot b B (Complex.I*(ε:ℂ)) q‖ := by
  obtain ⟨c,hcpos,hgap⟩ := edgeParamRoot_uniform_gap (b := b) hB hc
  have ht : Tendsto (fun ε : ℝ => Complex.I*(ε:ℂ)) (𝓝 0) (𝓝 0) := by
    have hh : Continuous (fun ε : ℝ => Complex.I*(ε:ℂ)) := by fun_prop
    have ht' : Tendsto (fun ε : ℝ => Complex.I*(ε:ℂ)) (𝓝 0) (𝓝 (Complex.I*(0:ℂ))) := hh.continuousAt
    simpa using ht' 
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (ht.eventually hgap)
  refine ⟨c,δ,hcpos,hδ,?_⟩
  intro ε hε hεδ q hq
  have hm := hδsub (show ε∈ball (0:ℝ) δ by simpa [Real.dist_eq,abs_of_pos hε] using hεδ)
  have hi : (Complex.I*(ε:ℂ)).im=ε := by simp
  simpa only [hi] using hm q hq (by simpa only [hi] using hε)


theorem edgeParamRoot_inward_exponential {b : ℝ} {B : ℂ→ℂ}
    (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ ε : ℝ, 0<ε → ε<δ → ∀ q∈Icc (-Real.pi) Real.pi,
      ‖edgeParamRoot b B (Complex.I*(ε:ℂ)) q‖≤Real.exp (-c*(ε+q^2)) := by
  obtain ⟨c,δ,hcpos,hδ,hgap⟩ := edgeParamRoot_inward_gap (b := b) hB hc
  refine ⟨c,δ,hcpos,hδ,?_⟩
  intro ε hε hεδ q hq
  have hg := hgap ε hε hεδ q hq
  have he := Real.add_one_le_exp (-c*(ε+q^2))
  linarith

end
end IsingBulk.Anisotropic.RegularEdges
