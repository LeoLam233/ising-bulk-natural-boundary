import IsingBulk.Anisotropic.NegativeNormalForm.ActualDensityBetaUniform

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Filter
open scoped Topology

/-- The actual uniform density error vanishes on any growing-order sequence
with N²/j→0. This includes the selected j of order N² log N. -/
theorem betaDensityScale_tendsto_zero (N j : ℕ → ℕ) (A : ℝ)
    (horder : Tendsto (fun k => (j k:ℝ)) atTop atTop)
    (hratio : Tendsto (fun k => (N k:ℝ)^2/(j k:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => A*((N k:ℝ)/Real.sqrt (j k)+(N k:ℝ)^2/(j k:ℝ)+
      Real.exp (-(j k:ℝ)*Real.log 2/8))) atTop (𝓝 0) := by
  have hroot : Tendsto (fun k => (N k:ℝ)/Real.sqrt (j k)) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
    change Tendsto (fun k => Real.sqrt ((N k:ℝ)^2/(j k:ℝ))) atTop (𝓝 (Real.sqrt 0)) at hh
    have he : (fun k => Real.sqrt ((N k:ℝ)^2/(j k:ℝ)))=
        (fun k => (N k:ℝ)/Real.sqrt (j k)) := by
      funext k
      rw [Real.sqrt_div (by positivity : 0≤(N k:ℝ)^2),Real.sqrt_sq (by positivity : 0≤(N k:ℝ))]
    rw [he,Real.sqrt_zero] at hh
    exact hh
  have hlog : 0<Real.log 2/8 := by apply div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have he0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (horder.atTop_mul_const hlog)
  have he : Tendsto (fun k => Real.exp (-(j k:ℝ)*Real.log 2/8)) atTop (𝓝 0) := by
    convert he0 using 1
    funext k
    congr 1
    ring
  simpa only [zero_add,add_zero,mul_zero] using ((hroot.add hratio).add he).const_mul A

end
end IsingBulk.Anisotropic.NegativeNormalForm
