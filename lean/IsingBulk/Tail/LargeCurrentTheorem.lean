import IsingBulk.Tail.ProtectedTheorem
import IsingBulk.Tail.ProtectedLargeCurrentTransfer

/-! Actual large-lambda differentiated current estimate. The complete
current is differentiated on a common disk before the fixed lambda split;
all source envelopes are proved, not hypotheses of this theorem. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric MeasureTheory
open scoped Topology
set_option maxHeartbeats 1500000

theorem large_current_per_order (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ, 0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,
        0<α → α<α₀ → 0<τ → τ<τ₀ →
        ∃ c eps₀ K D κ : ℝ, 0<c ∧ 0<eps₀ ∧ 0<K ∧ 0<D ∧ 0<κ ∧
          ∀ (N j : ℕ) (eps lamStar : ℝ),
            1≤N → 0<eps → eps<eps₀ → 0<lamStar → lamStar≤1 →
            IntervalIntegrable (fun lam => differentiatedCurrentSlice N (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)) volume lamStar 1 ∧
            ‖∫ lam in lamStar..1, differentiatedCurrentSlice N (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)‖≤
              ((j.factorial:ℝ)*K/c^j)*(N:ℝ)^(2*j)*D^N*Real.exp (-κ*(N:ℝ)^2)*(lamStar⁻¹)^(j+1) := by
  obtain ⟨ηP,hηP,hP⟩ := protected_current_disk_and_envelope d hcsmall
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨epsR,hepsR,_,hmargin⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hsetup⟩ := hP η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  obtain ⟨c,e,K,D,κ,hc,he,hK,hD,hκ,hsource⟩ := hsetup α τ hα hαlt hτ hτlt
  refine ⟨c,min e epsR,K,D,κ,hc,lt_min he hepsR,hK,hD,hκ,?_⟩
  intro N j eps lamStar hN heps hepslt hls hls1
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hreg := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hmarg : r⁻¹-r<(sourceS (radialParameter d.theta eps)).im := by
    have hh := radialRadius_parameter_margin heps (hmargin eps heps (hepslt.trans_le (min_le_right _ _)))
    change r⁻¹-r+Real.sin d.theta*eps<_ at hh
    linarith [mul_pos hsint heps]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hδ : 0<c*lamStar/(N:ℝ)^2 := by positivity
  have hB : 0≤K*D^N*Real.exp (-κ*(N:ℝ)^2) := by positivity
  have hh := actual_large_current_cauchy_integral N (by omega) f hr hr1 hτ.le
    hreg.p_smooth hreg.m_smooth hreg.a_smooth hreg.p_nonneg hreg.m_nonneg hreg.m_le_one
    hreg.p_zero hreg.m_zero hmarg hδ hls hls1 hB
    (fun lam hlam => (hsource N eps lamStar lam hN heps (hepslt.trans_le (min_le_left _ _)) hls hlam.1 hlam.2).1)
    (fun lam hlam s hs => by
      have hb := (hsource N eps lamStar lam hN heps (hepslt.trans_le (min_le_left _ _)) hls hlam.1 hlam.2).2 s hs
      convert hb using 1
      simp only [div_eq_mul_inv,inv_pow]
      ring) j
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1
  simp only [div_eq_mul_inv,mul_inv_rev,mul_pow,inv_pow,inv_inv,pow_succ,pow_mul]
  ring

end
end IsingBulk.Tail
