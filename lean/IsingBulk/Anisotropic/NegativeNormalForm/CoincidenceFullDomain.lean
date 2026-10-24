import IsingBulk.Anisotropic.NegativeNormalForm.HadamardFullDomain
import IsingBulk.Anisotropic.NegativeNormalForm.CoincidenceFactors

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

 theorem collisionInsert_segment_norm {n : ℕ} (i j : Fin n) (v : Config n)
    (s : ℝ) (hs : s∈Icc 0 1) :
    ‖collisionInsert i j (coordinateContraction s (v,v i-v j))‖≤‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro k
  simp only [collisionInsert_apply,coordinateContraction_apply]
  by_cases hk : k=i
  · simp only [hk,ite_true]
    have he : v j+(s:ℂ)*(v i-v j)=((1-s:ℝ):ℂ)*v j+(s:ℂ)*v i := by push_cast; ring
    rw [he]
    have h := norm_add_le (((1-s:ℝ):ℂ)*v j) ((s:ℂ)*v i)
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1,
      abs_of_nonneg (sub_nonneg.mpr hs.2)] at h
    have hi := norm_le_pi_norm v i
    have hj := norm_le_pi_norm v j
    nlinarith [hs.1,hs.2]
  · simpa only [ite_eq_right hk] using norm_le_pi_norm v k

 theorem collisionFunction_analyticAt_point {n : ℕ} (Phi : Config n → Config n)
    (i j : Fin n) (z : Config n × ℂ) (hPhi : AnalyticAt ℂ Phi (collisionInsert i j z)) :
    AnalyticAt ℂ (collisionFunction Phi i j) z := by
  have h := hPhi.comp (f := collisionInsert i j) ((collisionInsert i j).analyticAt z)
  exact (analyticAt_pi_iff.mp h i).sub (analyticAt_pi_iff.mp h j)

/-- Exact divisor factorization on the whole common ball, not just an eventual germ. -/
theorem coincidenceFactor_identity_on_ball {n : ℕ} (Phi : Config n → Config n) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (i j : Fin n) (hij : i≠j) (v : Config n) (hv : ‖v‖<r) :
    Phi v i-Phi v j=(v i-v j)*coincidenceFactor Phi i j v := by
  have hseg (s : ℝ) (hs : s∈Icc 0 1) :
      AnalyticAt ℂ (collisionFunction Phi i j) (coordinateContraction s (v,v i-v j)) := by
    apply collisionFunction_analyticAt_point
    apply hPhi
    simpa only [mem_ball,dist_zero_right] using (collisionInsert_segment_norm i j v s hs).trans_lt hv
  have h := coordinateHadamard_identity_on_segment (v,v i-v j) hseg
  have hz : collisionFunction Phi i j (v,0)=0 := sub_eq_zero.mpr
    (equivariant_coincidence Phi heq _ i j (collisionInsert_coincidence i j hij v))
  rw [hz,sub_zero] at h
  simpa only [collisionFunction,collisionInsert_reconstruct,coincidenceFactor] using h

/-- Actual collision factors are holomorphic throughout the full original ball.
The axis case is proved by translating the Hadamard integral, not by division. -/
theorem coincidenceFactor_analyticOnNhd {n : ℕ} (Phi : Config n → Config n) (r : ℝ)
    (hPhi : AnalyticOnNhd ℂ Phi (ball 0 r))
    (heq : ∀ e v, Phi (permute e v)=permute e (Phi v))
    (i j : Fin n) (hij : i≠j) :
    AnalyticOnNhd ℂ (coincidenceFactor Phi i j) (ball 0 r) := by
  intro v hv
  have hv' : ‖v‖<r := by simpa using hv
  have harg : AnalyticAt ℂ (fun w : Config n => (w,w i-w j)) v :=
    analyticAt_id.prod ((analyticAt_pi_iff.mp analyticAt_id i).sub (analyticAt_pi_iff.mp analyticAt_id j))
  by_cases hsame : v i=v j
  · have he : collisionInsert i j (v,0)=v := by simpa only [hsame,sub_self] using collisionInsert_reconstruct i j v
    have ha : AnalyticAt ℂ (collisionFunction Phi i j) (v,0) :=
      collisionFunction_analyticAt_point Phi i j (v,0) (he.symm ▸ hPhi v hv)
    exact (coordinateHadamard_analyticAt_axis v ha).comp_of_eq harg (by simp [hsame])
  · have hn : v i-v j≠0 := sub_ne_zero.mpr hsame
    have hnum := (analyticAt_pi_iff.mp (hPhi v hv) i).sub (analyticAt_pi_iff.mp (hPhi v hv) j)
    have hden : AnalyticAt ℂ (fun w : Config n => w i-w j) v :=
      (analyticAt_pi_iff.mp analyticAt_id i).sub (analyticAt_pi_iff.mp analyticAt_id j)
    apply (hnum.div hden hn).congr
    filter_upwards [isOpen_ball.mem_nhds hv,hden.continuousAt.eventually_ne hn] with w hw hwn
    apply (div_eq_iff hwn).mpr
    simpa only [mul_comm,Pi.sub_apply] using coincidenceFactor_identity_on_ball Phi r hPhi heq i j hij w (by simpa using hw)

end
end IsingBulk.Anisotropic.NegativeNormalForm
