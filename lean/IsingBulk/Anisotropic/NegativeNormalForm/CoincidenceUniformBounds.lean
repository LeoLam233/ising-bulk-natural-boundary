import IsingBulk.Anisotropic.NegativeNormalForm.CoincidenceFullDomain
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedUniformEstimates

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

 theorem norm_sub_permute_swap {n : ℕ} (v : Config n) (i j : Fin n) :
    ‖v-permute (Equiv.swap i j) v‖=‖v i-v j‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    by_cases hki : k=i
    · subst k; simp [permute]
    by_cases hkj : k=j
    · subst k; simp [permute,norm_sub_rev]
    simp [permute,Equiv.swap_apply_of_ne_of_ne hki hkj]
  · simpa [permute] using norm_le_pi_norm (v-permute (Equiv.swap i j) v) i

 theorem coincidenceFactor_close_off_diagonal {n : ℕ} (Phi : Config n → Config n) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r)) (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (c : NNReal) (hLip : LipschitzOnWith c (fun v => Phi v-v) (closedBall 0 r))
    (i j : Fin n) (hij : i≠j) (v : Config n) (hv : ‖v‖<r) (hne : v i≠v j) :
    ‖coincidenceFactor Phi i j v-1‖≤(c:ℝ) := by
  have hs : permute (Equiv.swap i j) v∈closedBall 0 r := by simpa using hv.le
  have h := hLip.dist_le_mul v (by simpa using hv.le) (permute (Equiv.swap i j) v) hs
  simp only [dist_eq_norm,norm_sub_permute_swap] at h
  have hi := (norm_le_pi_norm ((Phi v-v)-(Phi (permute (Equiv.swap i j) v)-permute (Equiv.swap i j) v)) i).trans h
  have he : ((Phi v-v)-(Phi (permute (Equiv.swap i j) v)-permute (Equiv.swap i j) v)) i=
      (Phi v i-Phi v j)-(v i-v j) := by rw [heq]; simp [permute]; ring
  rw [he,coincidenceFactor_identity_on_ball Phi r hPhi heq i j hij v hv] at hi
  have hm : (v i-v j)*coincidenceFactor Phi i j v-(v i-v j)=(v i-v j)*(coincidenceFactor Phi i j v-1) := by ring
  rw [hm,norm_mul,mul_comm (c:ℝ)] at hi
  exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).mp (by simpa only [mul_comm] using hi)

/-- Complete pair multipliers stay uniformly near one even on every collision divisor. -/
theorem coincidenceFactor_uniform_close {n : ℕ} (Phi : Config n → Config n) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r)) (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (c : NNReal) (hLip : LipschitzOnWith c (fun v => Phi v-v) (closedBall 0 r))
    (i j : Fin n) (hij : i≠j) (v : Config n) (hv : ‖v‖<r) :
    ‖coincidenceFactor Phi i j v-1‖≤(c:ℝ) := by
  by_cases hsame : v i=v j
  · let b : Config n := fun k => if k=i then 1 else 0
    let x : ℂ → Config n := fun z => v+z • b
    have hx0 : x 0=v := by simp [x]
    have hx : ContinuousAt x 0 := by dsimp [x]; fun_prop
    have ht : Tendsto x (𝓝[≠] (0:ℂ)) (𝓝 v) := by simpa only [hx0] using hx.tendsto.mono_left nhdsWithin_le_nhds
    have hcf := coincidenceFactor_analyticOnNhd Phi r hPhi heq i j hij v (by simpa using hv)
    have hlim : Tendsto (fun z => ‖coincidenceFactor Phi i j (x z)-1‖) (𝓝[≠] (0:ℂ))
        (𝓝 ‖coincidenceFactor Phi i j v-1‖) :=
      ((hcf.continuousAt.tendsto.comp ht).sub (tendsto_const_nhds (x := (1:ℂ)))).norm
    apply le_of_tendsto hlim
    have hxb := ht.eventually (isOpen_ball.mem_nhds (show v∈ball (0:Config n) r by simpa using hv))
    filter_upwards [hxb,self_mem_nhdsWithin] with z hz hzne
    apply coincidenceFactor_close_off_diagonal Phi r hPhi heq c hLip i j hij (x z) (by simpa using hz)
    have hdiff : x z i-x z j=z := by
      simp only [x,Pi.add_apply,Pi.smul_apply,smul_eq_mul,b,ite_true,ite_eq_right (Ne.symm hij),mul_one,mul_zero,add_zero,hsame]
      ring
    apply sub_ne_zero.mp
    rw [hdiff]
    exact hzne
  · exact coincidenceFactor_close_off_diagonal Phi r hPhi heq c hLip i j hij v hv hsame

end
end IsingBulk.Anisotropic.NegativeNormalForm
