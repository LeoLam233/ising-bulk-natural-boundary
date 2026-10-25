import IsingBulk.Joint.Negative.UpperChart
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Transverse.CurveCoordinates
import IsingBulk.Anisotropic.RegularEdges.LocalFourthRoot

/-! Constructed upper coordinates for a genuinely variable-anisotropy negative
curve. The record contains only local coordinate identities and analytic units.
No coefficient bound, radius, or obstruction is among its fields. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.RegularEdges
open scoped Topology

structure UpperNormalization (curve : ℂ→Coupling) (amp : ℂ→ℂ) (b : ℝ) where
  Z : ℂ→Coupling
  weight : ℂ→ℂ
  f : ℂ→ℂ
  radius : ℝ
  radius_pos : 0<radius
  Z_analytic : AnalyticOnNhd ℂ Z (ball 0 radius)
  weight_analytic : AnalyticOnNhd ℂ weight (ball 0 radius)
  f_analytic : AnalyticAt ℂ f 0
  f_zero : f 0=0
  S_ne : ∀u∈ball 0 radius,S (Z u)≠0
  weight_ne : ∀u∈ball 0 radius,weight u≠0
  B_pos : ∀u∈ball 0 radius,0<(negativeChartB Z u).im
  edge : ∀u∈ball 0 radius,transferC (Z u)+transferB (Z u)=(b:ℂ)+u
  square : ∀u∈ball 0 radius,weight u^2=p (Z u)
  curve_eq : curve =ᶠ[𝓝 (0:ℂ)] (fun t=>Z (f t))
  weight_eq : amp =ᶠ[𝓝 (0:ℂ)] (fun t=>weight (f t))
  inward : ∀ᶠε : ℝ in 𝓝[>] 0,f (-(ε:ℂ))∈upperBall radius

/-- All upper-coordinate data are constructed from the actual normalized
negative curve and its actual analytic square root. -/
theorem exists_upperNormalization {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve 0) (ha : AnalyticAt ℂ amp 0)
    (hs : S (curve 0)≠0) (hamp : amp 0≠0)
    (hB : (transferB (curve 0)).im<0)
    (he : ∀ᶠt in 𝓝 (0:ℂ),transferC (curve t)+transferB (curve t)=
      (b:ℂ)+transferB (curve t)*t)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),amp t^2=p (curve t)) :
    Nonempty (UpperNormalization curve amp b) := by
  let f : ℂ→ℂ := fun t=>curveB curve t*t
  have hb := curveB_analyticAt hc hs
  have hf : AnalyticAt ℂ f 0 := hb.mul analyticAt_id
  have hf0 : f 0=0 := by simp [f]
  have hfd : deriv f 0=curveB curve 0 := by
    have h := (hb.differentiableAt.hasDerivAt.mul (hasDerivAt_id (0:ℂ))).deriv
    change deriv (curveB curve * id) 0=curveB curve 0
    simpa using h
  obtain ⟨psi,hpsi,hpsi0,hpr,hpl⟩ := Transverse.exists_nonramified_inverse hf hf0
    (by rw [hfd]; exact transferB_ne_zero_of_im_neg hB)
  let Z : ℂ→Coupling := fun u=>curve (psi u)
  let w : ℂ→ℂ := fun u=>amp (psi u)
  have hZ : AnalyticAt ℂ Z 0 := hc.comp_of_eq hpsi hpsi0
  have hw : AnalyticAt ℂ w 0 := ha.comp_of_eq hpsi hpsi0
  have hZ0 : Z 0=curve 0 := by simp [Z,hpsi0]
  have hw0 : w 0=amp 0 := by simp [w,hpsi0]
  have hSz : AnalyticAt ℂ (fun u=>S (Z u)) 0 := negativeChartS_analyticAt hZ
  have hBn : AnalyticAt ℂ (negativeChartB Z) 0 :=
    negativeChartB_analyticAt hZ (by rwa [hZ0])
  have hBn0 : 0<(negativeChartB Z 0).im := by
    simpa only [negativeChartB,hZ0,neg_div,Complex.neg_im,transferB,neg_pos] using hB
  have hev : ∀ᶠu in 𝓝 (0:ℂ),AnalyticAt ℂ Z u ∧ AnalyticAt ℂ w u ∧
      S (Z u)≠0 ∧ w u≠0 ∧ 0<(negativeChartB Z u).im ∧
      transferC (Z u)+transferB (Z u)=(b:ℂ)+u ∧ w u^2=p (Z u) := by
    have hp := hpsi.continuousAt.tendsto
    rw [hpsi0] at hp
    filter_upwards [hZ.eventually_analyticAt,hw.eventually_analyticAt,
      hSz.continuousAt.eventually_ne (by rwa [hZ0]),
      hw.continuousAt.eventually_ne (by rwa [hw0]),
      (Complex.continuous_im.continuousAt.comp hBn.continuousAt).eventually_const_lt hBn0,
      hp.eventually he,hp.eventually hsq,hpr] with u hZu hwu hSu hwu0 hBu heu hsqu hpu
    refine ⟨hZu,hwu,hSu,hwu0,hBu,?_,hsqu⟩
    change transferC (curve (psi u))+transferB (curve (psi u))=_
    rw [heu]
    exact congrArg (fun v : ℂ=>(b:ℂ)+v) hpu
  obtain ⟨r,hr,hrdata⟩ := Metric.mem_nhds_iff.mp hev
  have hcurve : curve =ᶠ[𝓝 (0:ℂ)] (fun t=>Z (f t)) :=
    hpl.mono (fun t ht=>by simp only [Z,ht])
  have hweight : amp =ᶠ[𝓝 (0:ℂ)] (fun t=>w (f t)) :=
    hpl.mono (fun t ht=>by simp only [w,ht])
  have hpath : Tendsto (fun ε : ℝ=>-(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun ε : ℝ=>-(ε:ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero,neg_zero] using
      (h.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have hfp : Tendsto (fun ε : ℝ=>f (-(ε:ℂ))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hf0,Function.comp_def] using hf.continuousAt.tendsto.comp hpath
  refine ⟨{
    Z := Z
    weight := w
    f := f
    radius := r
    radius_pos := hr
    Z_analytic := fun u hu=>(hrdata hu).1
    weight_analytic := fun u hu=>(hrdata hu).2.1
    f_analytic := hf
    f_zero := hf0
    S_ne := fun u hu=>(hrdata hu).2.2.1
    weight_ne := fun u hu=>(hrdata hu).2.2.2.1
    B_pos := fun u hu=>(hrdata hu).2.2.2.2.1
    edge := fun u hu=>(hrdata hu).2.2.2.2.2.1
    square := fun u hu=>(hrdata hu).2.2.2.2.2.2
    curve_eq := hcurve
    weight_eq := hweight
    inward := ?_ }⟩
  filter_upwards [hfp.eventually (ball_mem_nhds (0:ℂ) hr),
    inward_ray_eventually_mem hb.continuousAt hB (r:=1) (by norm_num)] with ε hnorm hside
  exact ⟨hnorm,hside.2⟩

/-- Positivity of every transfer dispersion excludes the literal spectral set. -/
theorem outside_spectralSet_of_transferW_im_pos {K : Coupling} (hS : S K≠0)
    (hi : ∀q : ℝ,0<(transferW K (q:ℂ)).im) : K∉spectralSet := by
  rintro ⟨a,ha,b,hb,he⟩
  have hw : transferW K ((Real.arccos b:ℝ):ℂ)=(a:ℂ) := by
    unfold transferW
    rw [←Complex.ofReal_cos,Real.cos_arccos hb.1 hb.2,he]
    field_simp
    ring
  have hh := hi (Real.arccos b)
  rw [hw,Complex.ofReal_im] at hh
  exact lt_irrefl _ hh

end
end IsingBulk.Joint.Negative
