import IsingBulk.Anisotropic.NegativeCycles.FixedDiskPoleRemainder
import IsingBulk.Anisotropic.NegativeCycles.CothUniversalRemainder

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric NegativeNormalForm

def cothPoleRemainder (n : ℕ) (R₀ f H : ℂ → ℂ) (T t : ℂ) : ℂ :=
  H t*R₀ ((n:ℂ)*f t)+parameterPoleRemainder n f H T t

theorem uniform_coth_subtraction {f H R₀ : ℂ → ℂ} {r η ρ M K : ℝ} {c T : ℂ}
    (n : ℕ) (hn : n≠0) (hr : 0<r) (hηr : η≤r/2) (hc : c≠0) (hM : 0≤M)
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (h0 : f T=0)
    (hb : ∀ z∈ball 0 r, ‖deriv f z-c‖≤‖c‖/4) (hT : ‖T‖≤r/2)
    (hH : AnalyticOnNhd ℂ H (ball 0 r)) (hbound : ∀ z∈ball 0 r, ‖H z‖≤M)
    (hR₀ : AnalyticOnNhd ℂ R₀ (ball 0 ρ)) (hRbound : ∀ z∈ball 0 ρ, ‖R₀ z‖≤K)
    (hReq : ∀ z : ℂ, z≠0 → cothHalf id z=2/z+R₀ z)
    (hphase : ∀ t∈ball 0 η, ‖(n:ℂ)*f t‖<ρ) :
    ∃ R : ℂ → ℂ, R=cothPoleRemainder n R₀ f H T ∧ AnalyticOnNhd ℂ R (ball 0 η) ∧
      (∀ t∈ball 0 η, ‖R t‖≤M*(K+16/((n:ℝ)*‖c‖*r))) ∧
      ∀ t∈ball 0 η, t≠T →
        H t*cothHalf (fun u => (n:ℂ)*f u) t=
          (2*H T/((n:ℂ)*deriv f T))/(t-T)+R t := by
  obtain ⟨R₁,hR₁,hRa,hRb,hRe⟩ := exists_fixed_disk_pole_remainder n hn hr hc hM hf h0 hb hT hH hbound
  have hsub : ball (0:ℂ) η⊆ball 0 r := ball_subset_ball (by linarith)
  have hhalf (t : ℂ) (ht : t∈ball 0 η) : ‖t‖≤r/2 :=
    (show ‖t‖<η by simpa only [mem_ball,dist_zero_right] using ht).le.trans hηr
  let R : ℂ → ℂ := fun t => H t*R₀ ((n:ℂ)*f t)+R₁ t
  refine ⟨R,by funext t; simp only [R,cothPoleRemainder,hR₁],?_,?_,?_⟩
  · intro t ht
    have hfa : AnalyticAt ℂ (fun w => (n:ℂ)*f w) t := analyticAt_const.mul (hf t (hsub ht))
    have hRta : AnalyticAt ℂ R₀ ((n:ℂ)*f t) :=
      hR₀ _ (by simpa only [mem_ball,dist_zero_right] using hphase t ht)
    exact ((hH t (hsub ht)).mul (hRta.comp (f := fun w => (n:ℂ)*f w) hfa)).add (hRa t (hsub ht))
  · intro t ht
    have hprod : ‖H t*R₀ ((n:ℂ)*f t)‖≤M*K := by
      rw [norm_mul]
      exact mul_le_mul (hbound t (hsub ht))
        (hRbound _ (by simpa only [mem_ball,dist_zero_right] using hphase t ht)) (norm_nonneg _) hM
    have hh := norm_add_le (H t*R₀ ((n:ℂ)*f t)) (R₁ t)
    change ‖H t*R₀ ((n:ℂ)*f t)+R₁ t‖≤_
    calc
      _ ≤ M*K+16*M/((n:ℝ)*‖c‖*r) := hh.trans (add_le_add hprod (hRb t (hhalf t ht)))
      _ = _ := by ring
  · intro t ht htT
    have hTr : T∈ball (0:ℂ) r := by simpa only [mem_ball,dist_zero_right] using (show ‖T‖<r by linarith)
    have hAt := (normalized_phase_factor_bounds hc hf hb hTr).2 t (hsub ht) |>.2.2
    have hft : f t≠0 := by
      rw [normalized_phase_factorization h0 t]
      exact mul_ne_zero (sub_ne_zero.mpr htT) hAt
    have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
    have hct := hReq ((n:ℂ)*f t) (mul_ne_zero hn' hft)
    change Complex.cosh (((n:ℂ)*f t)/2)/Complex.sinh (((n:ℂ)*f t)/2)=_ at hct
    change H t*(Complex.cosh (((n:ℂ)*f t)/2)/Complex.sinh (((n:ℂ)*f t)/2))=_
    rw [hct,mul_add]
    have he : H t*(2/((n:ℂ)*f t))=2*H t/((n:ℂ)*f t) := by ring
    rw [he,hRe t (hsub ht) htT]
    dsimp [R]
    ring

end
end IsingBulk.Anisotropic.NegativeCycles
