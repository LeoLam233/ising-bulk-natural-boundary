import IsingBulk.Final.LocalExtension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Small exterior crescents at the unit circle are genuinely connected.
This supplies the local domain for arbitrary inverse-temperature sheets. -/
namespace IsingBulk.Final
noncomputable section
open Set Metric
open scoped Topology

def exteriorCrescent (z : ℂ) (r : ℝ) : Set ℂ := ball z r ∩ {s : ℂ | 1 < ‖s‖}
def exteriorCrescentCenter (z : ℂ) (r : ℝ) : ℂ := (1+r/2:ℝ) • z

theorem exteriorCrescentCenter_mem {z : ℂ} (hz : ‖z‖=1) {r : ℝ} (hr : 0 < r) :
    exteriorCrescentCenter z r ∈ exteriorCrescent z r := by
  have hq : 0 < 1+r/2 := by linarith
  constructor
  · rw [mem_ball_iff_norm]
    have he : exteriorCrescentCenter z r-z=(r/2:ℝ) • z := by
      unfold exteriorCrescentCenter
      module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hr),hz,mul_one]
    linarith
  · change 1 < ‖exteriorCrescentCenter z r‖
    simp only [exteriorCrescentCenter,norm_smul,Real.norm_eq_abs,abs_of_pos hq,hz,mul_one]
    linarith

theorem exteriorCrescent_inner_gap {z y : ℂ} (hz : ‖z‖=1) {r : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/2) (hy : y ∈ exteriorCrescent z r) :
    1 < inner ℝ (exteriorCrescentCenter z r) y := by
  have hyb : ‖y-z‖ < r := mem_ball_iff_norm.mp hy.1
  have hyn : 1 < ‖y‖ := hy.2
  have hdist : ‖y-z‖^2 < r^2 := by nlinarith [norm_nonneg (y-z)]
  have hsq := norm_sub_sq_real y z
  rw [hz] at hsq
  have hinner : 1-r^2/2 < inner ℝ z y := by
    rw [real_inner_comm y z]
    nlinarith [norm_nonneg y]
  have hr2 : r^2 ≤ r/2 := by nlinarith
  have hr3 : r^3 ≤ r/4 := by
    have hh := mul_le_mul_of_nonneg_left hr2 hr.le
    nlinarith
  have hq : 0 < 1+r/2 := by linarith
  have hm := mul_lt_mul_of_pos_left hinner hq
  have hg : 1 < (1+r/2)*(1-r^2/2) := by nlinarith
  exact hg.trans (by simpa only [exteriorCrescentCenter,real_inner_smul_left] using hm)

theorem exteriorCrescent_starConvex {z : ℂ} (hz : ‖z‖=1) {r : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/2) :
    StarConvex ℝ (exteriorCrescentCenter z r) (exteriorCrescent z r) := by
  have hc := exteriorCrescentCenter_mem hz hr
  intro y hy a b ha hb hab
  refine ⟨(convex_ball z r) hc.1 hy.1 ha hb hab,?_⟩
  change 1 < ‖a • exteriorCrescentCenter z r+b • y‖
  have hcn : 1 < ‖exteriorCrescentCenter z r‖ := hc.2
  have hyn : 1 < ‖y‖ := hy.2
  have hci := exteriorCrescent_inner_gap hz hr hrsmall hy
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_smul,one_smul,zero_add] using hyn
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hc2 : 1 < ‖exteriorCrescentCenter z r‖^2 := by nlinarith
  have hy2 : 1 ≤ ‖y‖^2 := by nlinarith
  have h1 := mul_lt_mul_of_pos_left hc2 (sq_pos_of_pos hap)
  have h2 := mul_le_mul_of_nonneg_left hy2 (sq_nonneg b)
  have h3 := mul_le_mul_of_nonneg_left hci.le (mul_nonneg ha hb)
  have hnorm := norm_add_sq_real (a • exteriorCrescentCenter z r) (b • y)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,
    real_inner_smul_left,real_inner_smul_right] at hnorm
  have hsq : 1 < ‖a • exteriorCrescentCenter z r+b • y‖^2 := by
    nlinarith [sq_nonneg (a+b-1)]
  have hn : 0 ≤ ‖a • exteriorCrescentCenter z r+b • y‖ := norm_nonneg _
  change 1 < ‖a • exteriorCrescentCenter z r+b • y‖
  nlinarith

theorem exteriorCrescent_isConnected {z : ℂ} (hz : ‖z‖=1) {r : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/2) : IsConnected (exteriorCrescent z r) :=
  ((exteriorCrescent_starConvex hz hr hrsmall).isPathConnected (exteriorCrescentCenter_mem hz hr)).isConnected

theorem exteriorCrescent_isOpen (z : ℂ) (r : ℝ) : IsOpen (exteriorCrescent z r) :=
  isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)


theorem norm_convex_combination_gt_one {x y : ℂ} (hx : 1 < ‖x‖) (hy : 1 < ‖y‖)
    (hxy : 1 < inner ℝ x y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    1 < ‖a • x+b • y‖ := by
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_smul,one_smul,zero_add] using hy
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hx2 : 1 < ‖x‖^2 := by nlinarith
  have hy2 : 1 ≤ ‖y‖^2 := by nlinarith
  have h1 := mul_lt_mul_of_pos_left hx2 (sq_pos_of_pos hap)
  have h2 := mul_le_mul_of_nonneg_left hy2 (sq_nonneg b)
  have h3 := mul_le_mul_of_nonneg_left hxy.le (mul_nonneg ha hb)
  have hnorm := norm_add_sq_real (a • x) (b • y)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,
    real_inner_smul_left,real_inner_smul_right] at hnorm
  have hsq : 1 < ‖a • x+b • y‖^2 := by nlinarith [sq_nonneg (a+b-1)]
  nlinarith [norm_nonneg (a • x+b • y)]

def axisCrescentCenter (z : ℂ) (r sigma : ℝ) : ℂ := exteriorCrescentCenter z r+(sigma*r/16:ℝ)

theorem axisCrescentCenter_mem {z : ℂ} (hz : ‖z‖=1) (haxis : z.re=0)
    {r sigma : ℝ} (hr : 0 < r) (hsigma : sigma^2=1) :
    axisCrescentCenter z r sigma ∈ exteriorCrescent z r ∩ {s : ℂ | 0 < sigma*s.re} := by
  have hsigabs : |sigma|=1 := by nlinarith [sq_abs sigma,abs_nonneg sigma]
  have hcre : (exteriorCrescentCenter z r).re=0 := by
    simp [exteriorCrescentCenter,Complex.real_smul,haxis]
  have hnshift : ‖(sigma*r/16:ℝ)‖=r/16 := by rw [Real.norm_eq_abs,abs_div,abs_mul,hsigabs,abs_of_pos hr]; norm_num
  have hcdist : ‖exteriorCrescentCenter z r-z‖=r/2 := by
    have he : exteriorCrescentCenter z r-z=(r/2:ℝ) • z := by unfold exteriorCrescentCenter; module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hr),hz,mul_one]
  have hcn : 1 < ‖exteriorCrescentCenter z r‖ := (exteriorCrescentCenter_mem hz hr).2
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [mem_ball_iff_norm]
    have he : axisCrescentCenter z r sigma-z=(exteriorCrescentCenter z r-z)+(sigma*r/16:ℝ) := by
      unfold axisCrescentCenter
      ring
    rw [he]
    have hb := norm_add_le (exteriorCrescentCenter z r-z) ((sigma*r/16:ℝ):ℂ)
    rw [hcdist,Complex.norm_real,hnshift] at hb
    linarith
  · change 1 < ‖axisCrescentCenter z r sigma‖
    have hh := norm_add_sq_real (exteriorCrescentCenter z r) ((sigma*r/16:ℝ):ℂ)
    have hi : inner ℝ (exteriorCrescentCenter z r) ((sigma*r/16:ℝ):ℂ)=0 := by
      simp [Complex.inner,Complex.mul_re,hcre]
    rw [hi,mul_zero,add_zero] at hh
    change ‖axisCrescentCenter z r sigma‖^2= _ at hh
    nlinarith [sq_nonneg ‖((sigma*r/16:ℝ):ℂ)‖,norm_nonneg (axisCrescentCenter z r sigma)]
  · change 0 < sigma*(axisCrescentCenter z r sigma).re
    simp only [axisCrescentCenter,Complex.add_re,Complex.ofReal_re,hcre,zero_add]
    have he : sigma*(sigma*r/16)=r/16 := by nlinarith [hsigma]
    rw [he]
    positivity

theorem axisCrescent_half_starConvex {z : ℂ} (hz : ‖z‖=1) (haxis : z.re=0)
    {r sigma : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/2) (hsigma : sigma^2=1) :
    StarConvex ℝ (axisCrescentCenter z r sigma)
      (exteriorCrescent z r ∩ {s : ℂ | 0 < sigma*s.re}) := by
  have hc := axisCrescentCenter_mem hz haxis hr hsigma
  intro y hy a b ha hb hab
  have hgap : 1 < inner ℝ (axisCrescentCenter z r sigma) y := by
    have hh := exteriorCrescent_inner_gap hz hr hrsmall hy.1
    have hp : 0 < (sigma*r/16)*y.re := by
      have ht := mul_pos (show 0 < r/16 by positivity) hy.2
      nlinarith
    simp only [axisCrescentCenter,inner_add_left,Complex.inner,Complex.mul_re,Complex.conj_re,
      Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im] at *
    linarith
  refine ⟨⟨(convex_ball z r) hc.1.1 hy.1.1 ha hb hab,
    norm_convex_combination_gt_one hc.1.2 hy.1.2 hgap ha hb hab⟩,?_⟩
  change 0 < sigma*(a • axisCrescentCenter z r sigma+b • y).re
  simp only [Complex.add_re,Complex.smul_re,smul_eq_mul]
  have hca : 0 < sigma*(axisCrescentCenter z r sigma).re := hc.2
  have hya : 0 < sigma*y.re := hy.2
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_mul,one_mul,zero_add] using hya
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 := mul_pos hap hca
    have h2 := mul_nonneg hb hya.le
    nlinarith

theorem axisCrescent_half_isConnected {z : ℂ} (hz : ‖z‖=1) (haxis : z.re=0)
    {r sigma : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/2) (hsigma : sigma^2=1) :
    IsConnected (exteriorCrescent z r ∩ {s : ℂ | 0 < sigma*s.re}) :=
  ((axisCrescent_half_starConvex hz haxis hr hrsmall hsigma).isPathConnected
    (axisCrescentCenter_mem hz haxis hr hsigma)).isConnected


theorem axis_unit_point_near {z : ℂ} (hz : ‖z‖=1) (haxis : z.re=0)
    {r sigma : ℝ} (hr : 0 < r) (hsigma : sigma^2=1) :
    ∃ w : ℂ, ‖w‖=1 ∧ w ∈ ball z r ∧ 0 < sigma*w.re := by
  let delta := r/4
  have hd : 0 < delta := by dsimp only [delta]; positivity
  have hsigabs : |sigma|=1 := by nlinarith [sq_abs sigma,abs_nonneg sigma]
  let v : ℂ := z+(sigma*delta:ℝ)
  have hnshift : ‖((sigma*delta:ℝ):ℂ)‖=delta := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,hsigabs,abs_of_pos hd,one_mul]
  have hin : inner ℝ z ((sigma*delta:ℝ):ℂ)=0 := by simp [Complex.inner,Complex.mul_re,haxis]
  have hnv1 : 1 ≤ ‖v‖ := by
    have hh := norm_add_sq_real z ((sigma*delta:ℝ):ℂ)
    rw [hz,hin,mul_zero,add_zero,hnshift] at hh
    change ‖v‖^2=1^2+delta^2 at hh
    nlinarith [norm_nonneg v,sq_nonneg delta]
  have hnv : 0 < ‖v‖ := by linarith
  have hnvhi : ‖v‖ ≤ 1+delta := by
    have hh := norm_add_le z ((sigma*delta:ℝ):ℂ)
    simpa only [hz,hnshift] using hh
  let w : ℂ := ‖v‖⁻¹ • v
  have hnw : ‖w‖=1 := by
    rw [show ‖w‖=‖(‖v‖⁻¹:ℝ)‖*‖v‖ by exact norm_smul _ _,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnv),inv_mul_cancel₀ hnv.ne']
  have hdist : ‖w-v‖ ≤ delta := by
    have he : w-v=(‖v‖⁻¹-1:ℝ) • v := by dsimp only [w]; module
    have hne : ‖v‖⁻¹-1 ≤ 0 := by
      have hh := (inv_le_one₀ hnv).mpr hnv1
      linarith
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonpos hne]
    have heq : -(‖v‖⁻¹-1)*‖v‖=‖v‖-1 := by field_simp; ring
    rw [heq]
    linarith
  refine ⟨w,hnw,?_,?_⟩
  · rw [mem_ball_iff_norm]
    have hvz : ‖v-z‖=delta := by simpa only [v,add_sub_cancel_left] using hnshift
    have hh := norm_add_le (w-v) (v-z)
    rw [sub_add_sub_cancel,hvz] at hh
    dsimp only [delta] at *
    linarith
  · change 0 < sigma*(‖v‖⁻¹ • v).re
    simp only [Complex.smul_re,smul_eq_mul,v,Complex.add_re,Complex.ofReal_re,haxis,zero_add]
    have heq : sigma*(‖v‖⁻¹*(sigma*delta))=‖v‖⁻¹*delta := by
      calc
        _ = ‖v‖⁻¹*delta*sigma^2 := by ring
        _ = _ := by rw [hsigma,mul_one]
    rw [heq]
    exact mul_pos (inv_pos.mpr hnv) hd


theorem unit_mem_closure_exteriorCrescent {z : ℂ} (hz : ‖z‖=1) {r : ℝ} (hr : 0 < r) :
    z ∈ closure (exteriorCrescent z r) := by
  rw [Metric.mem_closure_iff]
  intro d hd
  let t := min r d
  have ht : 0 < t := lt_min hr hd
  have hc := exteriorCrescentCenter_mem hz ht
  refine ⟨exteriorCrescentCenter z t,⟨(ball_subset_ball (min_le_left _ _)) hc.1,hc.2⟩,?_⟩
  have hh : dist (exteriorCrescentCenter z t) z < t := hc.1
  rw [dist_comm]
  exact hh.trans_le (min_le_right _ _)

end
end IsingBulk.Final
