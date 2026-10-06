import IsingBulk.Tail.AngularFinitePartition

/-! Actual fixed-weight angular parameter jets and their spatial
continuity on the original legal sheet, used for source measure bridges. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set Filter
open scoped Topology ContDiff

theorem weightedAngularIntegral_jets (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hlam : 0 ≤ lam)
    (w : (Fin N → ℝ) → ℂ) (hw : Continuous w) (s : ℂ) (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (weightedAngularIntegral N f r tau lam w) s =
      ∫ theta in angleBox N, w theta*iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s ∧
    Continuous (fun theta : Fin N → ℝ => w theta*iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s) := by
  let U := dampingDomain r
  let psi := deformedPoint (N := N) f r tau lam
  let chi := fun theta : Fin N → ℝ => w theta*(N.factorial:ℂ)⁻¹*
    (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*(angularJacobian f tau lam theta).det
  let F := continuedContourDensity N
  let G := fun z => ∫ theta in angleBox N, chi theta*F (z,psi theta)
  have hU : IsOpen U := dampingDomain_isOpen r
  have hpsi : Continuous psi := deformedPoint_continuous f r tau lam hf.p_smooth.continuous hf.m_smooth.continuous
  have hJ : Continuous (fun theta : Fin N → ℝ => angularJacobian f tau lam theta) :=
    (angularJacobian_joint_contDiff f tau hf.p_smooth hf.m_smooth).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hchi : Continuous chi := by dsimp [chi]; fun_prop
  have hupper (z : ℂ) (hz : z∈U) (theta : Fin N → ℝ) (i : Fin N) :
      0 < (sourceW z (psi theta i)).im := by
    have hb := sourceW_upper_of_margin hr hr1 hz.2 (deformedPoint_zero_norm f hr.le tau theta i)
    exact hb.trans_le (deformed_sourceW_im_ge hN f hr htau hlam theta z
      hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero i)
  have hF (z : ℂ) (hz : z∈U) (theta : Fin N → ℝ) : AnalyticAt ℂ F (z,psi theta) := by
    have hY := homotopy_y_gap_nonzero hN f hr hr1 htau hlam theta hf.p_nonneg hf.m_le_one
    have hZ : 1-coordinateProduct (fun i => selectedContinuedRoot z (psi theta i)) ≠ 0 := by
      apply one_sub_coordinateProduct_ne_zero hN
      intro i
      unfold selectedContinuedRoot
      rw [continuedRoot_eq_interiorRoot (hupper z hz theta i)]
      exact interiorRoot_norm_lt_one (hupper z hz theta i)
    exact continuedContourDensity_analyticAt hz.1 (deformedPoint_nonzero f hr.ne' tau lam theta)
      (fun i => Or.inl (Or.inl (hupper z hz theta i))) hY hZ
  have hpoint (z : ℂ) (hz : z∈U) (theta : Fin N → ℝ) :
      w theta*pulledDensity f r tau lam z theta=chi theta*F (z,psi theta) := by
    rw [← continuedPulledDensity_eq_original f r tau lam z theta (hupper z hz theta)]
    dsimp [chi,F,psi,continuedPulledDensity,continuedContourDensity]
    ring
  have hpointjet (theta : Fin N → ℝ) :
      w theta*iteratedDeriv j (fun z => pulledDensity f r tau lam z theta) s =
        chi theta*jointParameterJet F j (s,psi theta) := by
    have he : (fun z => w theta*pulledDensity f r tau lam z theta) =ᶠ[𝓝 s]
        (fun z => chi theta*F (z,psi theta)) := by
      filter_upwards [hU.mem_nhds hs] with z hz
      exact hpoint z hz theta
    have hj := he.iteratedDeriv_eq j
    simp only [iteratedDeriv_const_mul_field] at hj
    simpa only [jointParameterJet_eq,iteratedDeriv_eq_iterate] using hj
  have he : weightedAngularIntegral N f r tau lam w =ᶠ[𝓝 s] G := by
    filter_upwards [hU.mem_nhds hs] with z hz
    exact setIntegral_congr_fun measurableSet_Icc (fun theta _ => hpoint z hz theta)
  constructor
  · rw [he.iteratedDeriv_eq j]
    have hj := compact_analytic_shape_integral_iteratedDeriv (μ := volume) (K := angleBox N) isCompact_Icc hU F
      psi hpsi chi hchi (fun z hz theta _ => hF z hz theta) j s hs
    calc
      _ = ∫ theta in angleBox N, chi theta*jointParameterJet F j (s,psi theta) := by
        simpa only [G,jointParameterJet_eq,iteratedDeriv_eq_iterate,angleBox] using hj
      _ = _ := setIntegral_congr_fun measurableSet_Icc (fun theta _ => (hpointjet theta).symm)
  · simp_rw [hpointjet]
    apply hchi.mul
    apply continuous_iff_continuousAt.mpr
    intro theta
    exact ((jointParameterJet_analyticAt (hF s hs theta) j).continuousAt.comp
      (f := fun theta => (s,psi theta)) (continuous_const.prodMk hpsi).continuousAt)

end
end IsingBulk.Tail
