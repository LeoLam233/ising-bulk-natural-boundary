import IsingBulk.Anisotropic.NegativeCycles.NormalizedCapIdentity

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric Filter
open scoped BigOperators Topology
set_option maxHeartbeats 800000

/-- A common radius discharges the actual scalar quotient nonvanishing for every
constructed witness, not just a selected inverse germ. -/
theorem corrected_cap_scalar_uniform (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) (r C R : ℝ)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃δ : ℝ,0<δ ∧ δ<R/2 ∧ ∀n : ℕ, ∀d : ℂ, ‖d‖<δ →
      ∀P : UniformProjectedWitness B phi hphi n d r C,
      ∀J : UniformCorrectionWitness B phi hphi n d r C P R,
      centralHessian B phi d≠0 ∧ ∀y : Config n, ‖y‖≤δ →
        phaseParameterQuotient B phi hphi d (P.T (P.V (J.W y)))≠0 := by
  have hqa := phaseParameterQuotient_joint_origin_analyticAt B phi hphi hB
  have hq0 : phaseParameterQuotient B phi hphi 0 0≠0 := by
    have hc := phaseParameterQuotient_center B phi hphi 0 (by simpa using hB)
    simp only [Complex.cos_zero,sub_self] at hc
    rw [hc]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)) hBn
  obtain ⟨a,ha,hqn⟩ := Metric.mem_nhds_iff.mp (hqa.continuousAt.eventually_ne hq0)
  have htau : Tendsto (fun d : ℂ=>1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ=>1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  have hb : ∀ᶠd : ℂ in 𝓝 0,‖1-Complex.cos d‖<a/2 ∧ centralHessian B phi d≠0 := by
    filter_upwards [htau.eventually (ball_mem_nhds (0:ℂ) (by positivity : 0<a/2)),
      centralHessian_eventually_nonzero B phi hB] with d hd hh
    exact ⟨by simpa using hd,hh⟩
  obtain ⟨b,hb,hbs⟩ := Metric.mem_nhds_iff.mp hb
  let δ := min R (min a b)/16
  have hδ : 0<δ := div_pos (lt_min hR (lt_min ha hb)) (by norm_num)
  have hδR : 16*δ≤R := by dsimp [δ]; linarith [min_le_left R (min a b)]
  have hδa : 16*δ≤a := by
    have hh := (min_le_right R (min a b)).trans (min_le_left a b)
    dsimp [δ]; linarith
  have hδb : δ≤b := by
    have hh := (min_le_right R (min a b)).trans (min_le_right a b)
    dsimp [δ]; linarith
  refine ⟨δ,hδ,by linarith,?_⟩
  intro n d hd P J
  have hbd := hbs (show d∈ball (0:ℂ) b by simpa using hd.trans_le hδb)
  refine ⟨hbd.2,?_⟩
  intro y hy
  have hys : ‖y‖≤R/2 := by linarith
  have hf := (J.corrected_bounds B phi hphi d r C R P hr hR hRr).2 y hys
  have hvl : ‖P.V (J.W y)‖<2*r := by linarith [hf.1]
  have ht := P.t_lip (P.V (J.W y)) 0 hvl (by simpa using (show 0<2*r by positivity))
  rw [P.t_zero,sub_zero] at ht
  have hta : ‖P.T (P.V (J.W y))‖<a := by
    have h := norm_le_norm_sub_add (P.T (P.V (J.W y))) (1-Complex.cos d)
    linarith [hf.1,hbd.1]
  have hq := hqn (show (P.T (P.V (J.W y)),d)∈ball (0 : ℂ × ℂ) a by
    simpa only [mem_ball,dist_zero_right,Prod.norm_def] using max_lt hta (by linarith : ‖d‖<a))
  exact hq

/-- Exact cutoff cap normalization on a common ball, with all scalar-domain
conditions derived and no conditions on the inverse outside the cutoff. -/
theorem normalized_cutoff_cap_uniform (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) (r C R : ℝ)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃δ : ℝ,0<δ ∧ ∀n : ℕ, ∀d : ℝ, |d|<δ →
      ∀P : UniformProjectedWitness B phi hphi (n+1) (d:ℂ) r C,
      ∀J : UniformCorrectionWitness B phi hphi (n+1) (d:ℂ) r C P R,
      regularResidue B rootB phi hphi (d:ℂ) P.T 0≠0 →
      ∀j : ℕ, ∀b : ContDiffBump (0:ℝ), b.rOut≤δ^2 → ∀q : Fin n→ℝ,
      let Phi := fun y=>P.V (J.W y)
      (shapeSpatialCutoff b q:ℂ)*constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
        (constrainedMap Phi (complexify n q))*constrainedJacobian Phi (complexify n q)=
      regularResidue B rootB phi hphi (d:ℂ) P.T 0*(shapeSpatialCutoff b q:ℂ)*
        normalizedFullDensity B rootB phi hphi (d:ℂ) P.T Phi (complexify n q)*
        quadraticModelKernel n j (1-Real.cos d) (centralHessian B phi (d:ℂ)/(2*(n+1:ℕ))) q := by
  obtain ⟨δ,hδ,hδR,hscalar⟩ := corrected_cap_scalar_uniform B phi hphi hB hBn r C R hr hR hRr
  refine ⟨δ,hδ,?_⟩
  intro n d hd P J hcen j b hb q
  dsimp only
  by_cases hz : shapeSpatialCutoff b q=0
  · simp [hz]
  have hQ : constrainedSquaredRadius q≤δ^2 := by
    have hh : constrainedSquaredRadius q<b.rOut := by
      by_contra h
      exact hz (shapeSpatialCutoff_zero b (le_of_not_gt h))
    exact hh.le.trans hb
  have hnorm : ‖freeChartCLM n (complexify n q)‖≤δ := by
    rw [freeChartCLM_eq_shapeExtend]
    exact norm_shapeExtend_complexify_le q hδ.le hQ
  obtain ⟨hh,ha⟩ := hscalar (n+1) (d:ℂ) (by simpa using hd) P J
  have he := corrected_normalized_cap_pointwise B rootB phi hphi d r C R P J hr hR hRr hcen hh q
    (hnorm.trans_lt hδR) (ha _ hnorm) j
  dsimp only at he
  calc
    _=(shapeSpatialCutoff b q:ℂ)*
        (constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j
          (constrainedMap (fun y=>P.V (J.W y)) (complexify n q))*
          constrainedJacobian (fun y=>P.V (J.W y)) (complexify n q)) := by ring
    _=_ := by rw [he]; ring

end IsingBulk.Anisotropic.NegativeCycles
