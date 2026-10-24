import IsingBulk.Anisotropic.NegativeCycles.UniformDividedDifference

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric Filter NegativeNormalForm
open scoped Topology

theorem dslope_close_of_derivative_close {f : ℂ → ℂ} {r ε : ℝ} {c T t : ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hb : ∀ z∈ball 0 r, ‖deriv f z-c‖≤ε) (hT : T∈ball 0 r) (ht : t∈ball 0 r) :
    ‖dslope f T t-c‖≤ε := by
  by_cases he : t=T
  · subst t
    rw [dslope_same]
    exact hb T hT
  · let g : ℂ → ℂ := fun z => f z-c*z
    have hd (z : ℂ) (hz : z∈ball 0 r) : HasDerivAt g (deriv f z-c) z := by
      simpa only [g,Pi.sub_def,id_eq,mul_one] using
        (hf z hz).differentiableAt.hasDerivAt.sub ((hasDerivAt_id z).const_mul c)
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hd z hz).differentiableAt)
      (fun z hz => by rw [(hd z hz).deriv]; exact hb z hz) (convex_ball (0:ℂ) r) hT ht
    have hid : dslope f T t-c=(g t-g T)/(t-T) := by
      rw [dslope_of_ne _ he,slope_def_field]
      dsimp [g]
      field_simp
      ring
    rw [hid,norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mpr hh

theorem normalized_phase_factor_bounds {f : ℂ → ℂ} {r : ℝ} {c T : ℂ}
    (hc : c≠0) (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hb : ∀ z∈ball 0 r, ‖deriv f z-c‖≤‖c‖/4) (hT : T∈ball 0 r) :
    AnalyticOnNhd ℂ (dslope f T) (ball 0 r) ∧
      ∀ t∈ball 0 r, ‖dslope f T t-c‖≤‖c‖/4 ∧ ‖c‖/2≤‖dslope f T t‖ ∧ dslope f T t≠0 := by
  refine ⟨analyticOnNhd_dslope hf hT,?_⟩
  intro t ht
  have hclose := dslope_close_of_derivative_close hf hb hT ht
  have hnorm := norm_le_norm_sub_add c (dslope f T t)
  rw [norm_sub_rev c] at hnorm
  have hlo : ‖c‖/2≤‖dslope f T t‖ := by linarith [norm_nonneg c]
  exact ⟨hclose,hlo,norm_pos_iff.mp ((div_pos (norm_pos_iff.mpr hc) (by norm_num)).trans_le hlo)⟩

theorem normalized_phase_quotient_bounds {f H : ℂ → ℂ} {r M : ℝ} {c T : ℂ}
    (hc : c≠0) (hM : 0≤M) (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hb : ∀ z∈ball 0 r, ‖deriv f z-c‖≤‖c‖/4) (hT : T∈ball 0 r)
    (hH : AnalyticOnNhd ℂ H (ball 0 r)) (hbound : ∀ z∈ball 0 r, ‖H z‖≤M) :
    AnalyticOnNhd ℂ (fun t => H t/dslope f T t) (ball 0 r) ∧
      ∀ t∈ball 0 r, ‖H t/dslope f T t‖≤2*M/‖c‖ := by
  obtain ⟨ha,hs⟩ := normalized_phase_factor_bounds hc hf hb hT
  refine ⟨fun t ht => (hH t ht).div (ha t ht) (hs t ht).2.2,?_⟩
  intro t ht
  rw [norm_div]
  calc
    _ ≤ M/‖dslope f T t‖ := div_le_div_of_nonneg_right (hbound t ht) (norm_nonneg _)
    _ ≤ M/(‖c‖/2) := div_le_div_of_nonneg_left hM
      (div_pos (norm_pos_iff.mpr hc) (by norm_num)) (hs t ht).2.1
    _ = _ := by ring

theorem normalized_phase_factorization {f : ℂ → ℂ} {T : ℂ} (h0 : f T=0) (t : ℂ) :
    f t=(t-T)*dslope f T t := by
  simpa only [smul_eq_mul,h0,sub_zero] using (sub_smul_dslope f T t).symm

end
end IsingBulk.Anisotropic.NegativeCycles
