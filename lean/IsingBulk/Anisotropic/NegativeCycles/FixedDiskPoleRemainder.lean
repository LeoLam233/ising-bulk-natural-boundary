import IsingBulk.Anisotropic.NegativeCycles.NormalizedPhaseFactor

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric NegativeNormalForm

def parameterPoleRemainder (n : ℕ) (f H : ℂ → ℂ) (T t : ℂ) : ℂ :=
  (2/(n:ℂ))*dslope (fun u => H u/dslope f T u) T t

theorem exists_fixed_disk_pole_remainder {f H : ℂ → ℂ} {r M : ℝ} {c T : ℂ}
    (n : ℕ) (hn : n≠0) (hr : 0<r) (hc : c≠0) (hM : 0≤M)
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (h0 : f T=0)
    (hb : ∀ z∈ball 0 r, ‖deriv f z-c‖≤‖c‖/4) (hT : ‖T‖≤r/2)
    (hH : AnalyticOnNhd ℂ H (ball 0 r)) (hbound : ∀ z∈ball 0 r, ‖H z‖≤M) :
    ∃ R : ℂ → ℂ, R=parameterPoleRemainder n f H T ∧ AnalyticOnNhd ℂ R (ball 0 r) ∧
      (∀ t, ‖t‖≤r/2 → ‖R t‖≤16*M/((n:ℝ)*‖c‖*r)) ∧
      ∀ t∈ball 0 r, t≠T →
        2*H t/((n:ℂ)*f t)=(2*H T/((n:ℂ)*deriv f T))/(t-T)+R t := by
  have hTr : T∈ball (0:ℂ) r := by simpa only [mem_ball,dist_zero_right] using (show ‖T‖<r by linarith)
  obtain ⟨hA,hAs⟩ := normalized_phase_factor_bounds hc hf hb hTr
  obtain ⟨hQ,hQb⟩ := normalized_phase_quotient_bounds hc hM hf hb hTr hH hbound
  let Q : ℂ → ℂ := fun t => H t/dslope f T t
  let R : ℂ → ℂ := fun t => (2/(n:ℂ))*dslope Q T t
  refine ⟨R,rfl,fun t ht => analyticAt_const.mul (analyticOnNhd_dslope hQ hTr t ht),?_,?_⟩
  · intro t ht
    have hh := analytic_disk_dslope_bound hr hQ hQb hT ht
    change ‖(2/(n:ℂ))*dslope Q T t‖≤_
    rw [norm_mul,norm_div,Complex.norm_natCast,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    calc
      _ ≤ (2/(n:ℝ))*(4*(2*M/‖c‖)/r) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  · intro t ht htT
    have htn : t-T≠0 := sub_ne_zero.mpr htT
    have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
    have hAt := (hAs t ht).2.2
    have hAT : deriv f T≠0 := by simpa only [dslope_same] using (hAs T hTr).2.2
    have hs := sub_smul_dslope Q T t
    simp only [smul_eq_mul] at hs
    have hdivide : Q t/(t-T)=Q T/(t-T)+dslope Q T t := by
      apply (div_eq_iff htn).mpr
      rw [add_mul,div_mul_cancel₀ _ htn]
      linear_combination -hs
    have hleft : 2*H t/((n:ℂ)*f t)=(2/(n:ℂ))*(Q t/(t-T)) := by
      rw [normalized_phase_factorization h0 t]
      dsimp [Q]
      field_simp
    rw [hleft,hdivide,mul_add]
    change (2/(n:ℂ))*(Q T/(t-T))+R t=(2*H T/((n:ℂ)*deriv f T))/(t-T)+R t
    congr 1
    dsimp [Q]
    rw [dslope_same]
    ring

end
end IsingBulk.Anisotropic.NegativeCycles
