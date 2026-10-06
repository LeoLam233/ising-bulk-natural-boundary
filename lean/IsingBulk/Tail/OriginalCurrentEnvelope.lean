import IsingBulk.Tail.OriginalCurrentGlobalFactors
import IsingBulk.Tail.OriginalCurrentOneBody
import IsingBulk.Tail.OriginalCurrentCompletePair
import IsingBulk.Tail.CurrentDensityScale
import IsingBulk.Tail.ProtectedCurrentIntegrability

/-! Complete actual current envelope on the original c epsilon disk,
uniform on the entire fixed real lambda interval including zero. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem original_current_complete_envelope (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∃ c e K D κ : ℝ, 0 < c ∧ 0 < e ∧ 0 < K ∧ 0 < D ∧ 0 < κ ∧
        ∀ (N : ℕ) (eps lam : ℝ) (s : ℂ), 1 ≤ N → 0 < eps → eps < e →
          0 ≤ lam → lam ≤ 1 → ‖s-radialParameter d.theta eps‖ ≤ c*eps →
          (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps) < (sourceS s).im ∧
          ‖continuedCurrentSlice N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam s‖ ≤
            (K/eps^2)*D^N*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηV,τV,hηV,hτV,hV⟩ := original_current_actual_onebody_bound d hcsmall
  obtain ⟨ηP,hηP,hP⟩ := original_current_actual_complete_pair_product d hcsmall
  refine ⟨min ηP (min ηV (Real.sin d.thetaB/4)),
    lt_min hηP (lt_min hηV (by positivity [d.a_pos])),?_⟩
  intro η hη hηlt
  have hηp := hηlt.trans_le (min_le_left _ _)
  have hηv := hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηsmall := hηlt.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨αP,τP,hαP,hτP,hpairSetup⟩ := hP η hη hηp
  refine ⟨min αP (Real.sin d.thetaB/4),min τP τV,
    lt_min hαP (by positivity [d.a_pos]),lt_min hτP hτV,?_⟩
  intro α τ hα hαlt hτ hτlt
  have hαsmall := hαlt.trans_le (min_le_right _ _)
  obtain ⟨cP,eP,P,κ,hcP,heP,hPpos,hκ,hpair⟩ := hpairSetup α τ hα
    (hαlt.trans_le (min_le_left _ _)) hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨C,cV,eV,hC,hcV,heV,hvertex⟩ := hV η α τ hη hηv hα hαsmall hτ
    (hτlt.trans_le (min_le_right _ _))
  let f := constructedSelector d.thetaB η α
  have hreg := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cG,eG,A,G,hcG,_hcG1,heG,heG1,hA,hG,hglobal⟩ := original_current_global_factors
    d.theta d.c₀ τ hsint d.c₀_pos hcsmall hτ.le f hreg.p_nonneg
    (fun x => (thresholdStep_range _ _ _).2) hreg.m_nonneg hreg.m_le_one hreg.p_zero hreg.m_zero
  obtain ⟨J,hJ,hjac⟩ := constructed_selector_jacobian_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ.le
  obtain ⟨M,hM,hmult⟩ := constructed_current_multiplier_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ
  let c := min cG (min cP cV)
  let e := min eG (min eP eV)
  let E := Real.exp (d.c₀+2*τ)
  let D := (2*Real.pi)⁻¹*J*E*A*P
  let L := 4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi)
  have hD : 0 < D := by dsimp [D,E]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨c,e,2*M/G,D*L,κ,lt_min hcG (lt_min hcP hcV),lt_min heG (lt_min heP heV),
    by positivity,mul_pos hD hL,hκ,?_⟩
  intro N eps lam s hN heps hepslt hl0 hl1 hsd
  have heG' := hepslt.trans_le (min_le_left _ _)
  have heP' := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heV' := hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have heps1 : eps ≤ 1 := heG'.le.trans heG1
  have hsG := hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cG _) heps.le)
  have hsP := hsd.trans (mul_le_mul_of_nonneg_right ((min_le_right cG _).trans (min_le_left cP cV)) heps.le)
  have hsV := hsd.trans (mul_le_mul_of_nonneg_right ((min_le_right cG _).trans (min_le_right cP cV)) heps.le)
  have hg (θ : Fin N → ℝ) := hglobal N hN eps lam heps heG' hl0 hl1 θ s hsG
  have hmargin := (hg (fun _ => 0)).1
  refine ⟨hmargin,?_⟩
  let r := Real.exp (-d.c₀*eps)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hs : s ≠ 0 := (dampingDomain_of_margin hr hr1 hmargin).1
  have hphys (θ : Fin N → ℝ) (i : Fin N) : 0 < (sourceW s (deformedPoint f r τ lam θ i)).im := by
    have hb := sourceW_upper_of_margin hr hr1 hmargin (deformedPoint_zero_norm f hr.le τ θ i)
    exact hb.trans_le (deformed_sourceW_im_ge (by omega) f hr hτ.le hl0 θ s
      hreg.p_nonneg hreg.m_nonneg hreg.p_zero hreg.m_zero i)
  have hnon (θ : Fin N → ℝ) :
      (1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)))*
        (1-coordinateProduct (deformedPoint f r τ lam θ)) ≠ 0 :=
    norm_pos_iff.mp ((mul_pos hG (sq_pos_of_pos heps)).trans_le (hg θ).2.2)
  have hpoint (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      ‖continuedNamedCurrentDensity f r τ lam s q θ‖ ≤
        ((N.factorial:ℝ)⁻¹*(2*M/G/eps^2)*D^N*Real.exp (-κ*(N:ℝ)^2))*
          (∏ i,selectedOneBodyBound d.thetaB η C eps (θ i)) := by
    exact continuedNamedCurrentDensity_scale_bound f r τ lam s q θ _
      hA.le hPpos.le hG heps hJ.le (Real.exp_pos _).le hM.le
      (hg θ).2.1 (hg θ).2.2 (hpair N eps lam θ q s hN heps heP' hl0 hl1 hθ.1 hθ.2 hsP)
      (fun _ => selectedOneBodyBound_nonneg hC.le)
      (hvertex N eps lam θ q s hN heps heV' hl0 hl1 hθ.1 hθ.2 hsV)
      (fun i => (current_y_norm_envelope (by omega) f d.c₀_pos.le hτ.le heps.le heps1 hl0 hl1
        hreg.p_nonneg (fun x => (thresholdStep_range _ _ _).2) hreg.m_nonneg hreg.m_le_one θ i).1)
      (hjac N (by omega) lam hl0 hl1 θ) (hmult N q θ)
  have hint := continuedCurrentSlice_norm_le_onebody N f hr.ne' τ lam
    hreg.p_smooth hreg.m_smooth hreg.a_smooth hs d.thetaB_pos.le
    (by linarith [d.thetaB_lt,Real.pi_pos]) hC.le heps (by positivity)
    (fun _ θ _ i => Or.inl (Or.inl (hphys θ i)))
    (fun _ θ _ => (mul_ne_zero_iff.mp (hnon θ)).2)
    (fun _ θ _ => (mul_ne_zero_iff.mp (hnon θ)).1) hpoint
  have hnf : (N:ℝ)*(N.factorial:ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    apply (div_le_one (by exact_mod_cast Nat.factorial_pos N)).mpr
    exact_mod_cast Nat.self_le_factorial N
  calc
    _ ≤ (N:ℝ)*((N.factorial:ℝ)⁻¹*(2*M/G/eps^2)*D^N*Real.exp (-κ*(N:ℝ)^2))*L^N := hint
    _ = ((N:ℝ)*(N.factorial:ℝ)⁻¹)*((2*M/G/eps^2)*(D*L)^N*Real.exp (-κ*(N:ℝ)^2)) := by simp only [mul_pow]; ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hnf

end
end IsingBulk.Tail
