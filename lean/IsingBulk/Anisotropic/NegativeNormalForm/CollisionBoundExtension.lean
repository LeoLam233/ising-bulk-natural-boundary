import IsingBulk.Anisotropic.NegativeNormalForm.CoincidenceUniformBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators

/-- Extend a continuous real inequality through any coincidence hyperplane,
without imposing a smaller neighborhood or dividing on the hyperplane. -/
theorem le_on_ball_of_coordinate_ne {n : ℕ} (f g : Config n → ℝ) (r : ℝ)
    (i j : Fin n) (hij : i≠j) (v : Config n) (hv : ‖v‖<r) (hm : ZeroMean v)
    (hf : ContinuousAt f v) (hg : ContinuousAt g v)
    (haway : ∀ w : Config n, ‖w‖<r → ZeroMean w → w i≠w j → f w≤g w) : f v≤g v := by
  by_cases hsame : v i=v j
  · let b : Config n := fun k => (if k=i then 1 else 0)-(if k=j then 1 else 0)
    let x : ℂ → Config n := fun z => v+z • b
    have hb : ZeroMean b := by simp [ZeroMean,b,Finset.sum_sub_distrib]
    have hxm (z : ℂ) : ZeroMean (x z) := by
      change (∑ k, (v k+z*b k))=0
      rw [Finset.sum_add_distrib,← Finset.mul_sum,show ∑ k,v k=0 from hm,show ∑ k,b k=0 from hb]
      ring
    have hx0 : x 0=v := by simp [x]
    have hx : ContinuousAt x 0 := by dsimp [x]; fun_prop
    have ht : Tendsto x (𝓝[≠] (0:ℂ)) (𝓝 v) := by simpa only [hx0] using hx.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto (hf.tendsto.comp ht) (hg.tendsto.comp ht)
    have hxb := ht.eventually (isOpen_ball.mem_nhds (show v∈ball (0:Config n) r by simpa using hv))
    filter_upwards [hxb,self_mem_nhdsWithin] with z hz hzne
    apply haway (x z) (by simpa using hz) (hxm z)
    have hdiff : x z i-x z j=2*z := by
      simp only [x,Pi.add_apply,Pi.smul_apply,smul_eq_mul,b,ite_true,ite_eq_right (Ne.symm hij),ite_eq_right hij,mul_one,hsame,sub_zero,zero_sub,mul_neg,mul_one]
      ring
    apply sub_ne_zero.mp
    rw [hdiff]
    exact mul_ne_zero (by norm_num) hzne
  · exact haway v hv hm hsame

/-- Transfer the refined actual forward pair bound to the inverse Hadamard
factor. Only the continuous envelope must extend across a collision. -/
theorem coincidenceFactor_refined_from_forward {n : ℕ}
    (Phi : Config n → Config n) (r : ℝ) (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (c : NNReal) (hc : (c:ℝ)≤1)
    (hLip : LipschitzOnWith c (fun v => Phi v-v) (closedBall 0 r))
    (i j : Fin n) (hij : i≠j) (C : Config n → ℂ) (H : Config n → ℝ)
    (hH : ContinuousOn H (ball 0 r))
    (hforward : ∀ v, ‖v‖<r → ZeroMean v → (Phi v i-Phi v j)*C v=v i-v j)
    (hbound : ∀ v, ‖v‖<r → ZeroMean v → ‖C v-1‖≤H v)
    (v : Config n) (hv : ‖v‖<r) (hm : ZeroMean v) : ‖coincidenceFactor Phi i j v-1‖≤2*H v := by
  apply le_on_ball_of_coordinate_ne (fun w => ‖coincidenceFactor Phi i j w-1‖) (fun w => 2*H w)
    r i j hij v hv hm
  · exact ((coincidenceFactor_analyticOnNhd Phi r hPhi heq i j hij v (by simpa using hv)).continuousAt.sub continuousAt_const).norm
  · exact continuousAt_const.mul ((hH v (by simpa using hv)).continuousAt (isOpen_ball.mem_nhds (by simpa using hv)))
  · intro w hw hwm hne
    have hfac := coincidenceFactor_identity_on_ball Phi r hPhi heq i j hij w hw
    have hf := hforward w hw hwm
    rw [hfac,mul_assoc] at hf
    have hcancel : coincidenceFactor Phi i j w*C w=1 := by
      apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
      simpa only [mul_one] using hf
    have he : coincidenceFactor Phi i j w-1=coincidenceFactor Phi i j w*(1-C w) := by
      rw [mul_sub,mul_one,hcancel]
    have hn : ‖coincidenceFactor Phi i j w‖≤2 := by
      have hclose := coincidenceFactor_uniform_close Phi r hPhi heq c hLip i j hij w hw
      have ht := norm_sub_norm_le (coincidenceFactor Phi i j w) (1:ℂ)
      rw [norm_one] at ht
      linarith
    rw [he,norm_mul,norm_sub_rev (1:ℂ)]
    exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hbound w hw hwm) (by norm_num))

end
end IsingBulk.Anisotropic.NegativeNormalForm
