import IsingBulk.Tail.ProtectedCompletePairProduct
import IsingBulk.Tail.ProtectedCompleteDensity
import IsingBulk.Tail.ProtectedCurrentIntegrability

/-! Actual complete protected angular-current envelope. Every analytic,
root, complete-pair, one-body, multiplier and Jacobian estimate is derived
from the constructed selector; no sector bound is a premise. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem constructed_current_complete_envelope (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ, 0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,
        0<α → α<α₀ → 0<τ → τ<τ₀ →
        ∃ c eps₀ K D κ : ℝ, 0<c ∧ 0<eps₀ ∧ 0<K ∧ 0<D ∧ 0<κ ∧
          ∀ (N : ℕ) (eps lamStar lam : ℝ) (s : ℂ),
            1≤N → 0<eps → eps<eps₀ → 0<lamStar → lamStar≤lam → lam≤1 →
            ‖s-radialParameter d.theta eps‖≤c*lamStar/(N:ℝ)^2 →
            ‖continuedCurrentSlice N (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ lam s‖≤
              (K/lam^2)*D^N*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηR,τR,hηR,hτR,hR⟩ := constructed_current_actual_root_disk d hcsmall
  obtain ⟨ηV,τV,hηV,hτV,hV⟩ := protected_actual_onebody_bound d
  obtain ⟨ηP,hηP,hP⟩ := protected_actual_complete_pair_product d
  refine ⟨min ηP (min ηR (min ηV (Real.sin d.thetaB/4))),
    lt_min hηP (lt_min hηR (lt_min hηV (by positivity [d.a_pos]))),?_⟩
  intro η hη hηlt
  have hηp := hηlt.trans_le (min_le_left _ _)
  have hηr := hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηv := hηlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηsmall : η≤Real.sin d.thetaB/4 := hηlt.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨αP,τP,hαP,hτP,hpairSetup⟩ := hP η hη hηp
  refine ⟨min αP (Real.sin d.thetaB/4),min τP (min τR τV),
    lt_min hαP (by positivity [d.a_pos]),lt_min hτP (lt_min hτR hτV),?_⟩
  intro α τ hα hαlt hτ hτlt
  have hαsmall := hαlt.trans_le (min_le_right _ _)
  obtain ⟨cP,eP,P,κ,hcP,heP,hPpos,hκ,hpair⟩ := hpairSetup α τ hα
    (hαlt.trans_le (min_le_left _ _)) hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨cR,eR,aR,hcR,heR,haR,hroot⟩ := hR η α τ hη hηr hα hαsmall hτ
    (hτlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨C,cV,eV,hC,hcV,heV,hvertex⟩ := hV η α τ hη hηv hα hαsmall hτ
    (hτlt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨J,hJ,hjac⟩ := constructed_selector_jacobian_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ.le
  obtain ⟨M,hM,hmult⟩ := constructed_current_multiplier_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ
  let c := min cR (min cP (min cV (1/4:ℝ)))
  let e := min eR (min eP (min eV 1))
  let E := Real.exp (d.c₀+2*τ)
  let A := 21+4*E
  let G := aR*(3*τ/2)*Real.exp (-(aR+3*τ/2))
  let D := (2*Real.pi)⁻¹*J*E*A*P
  let L := 4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi)
  have hc : 0<c := lt_min hcR (lt_min hcP (lt_min hcV (by norm_num)))
  have he : 0<e := lt_min heR (lt_min heP (lt_min heV (by norm_num)))
  have hG : 0<G := by dsimp [G]; positivity
  have hD : 0<D := by dsimp [D,A,E]; positivity
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨c,e,2*M/G,D*L,κ,hc,he,by positivity,mul_pos hD hL,hκ,?_⟩
  intro N eps lamStar lam s hN heps hepslt hls hl hl1 hsd
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hn2 : 1≤(N:ℝ)^2 := by nlinarith
  have hlam : 0<lam := hls.trans_le hl
  have hdR := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left cR _) hls.le) (sq_nonneg (N:ℝ)))
  have hdP := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((min_le_right cR _).trans (min_le_left cP _)) hls.le) (sq_nonneg (N:ℝ)))
  have hdV := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((min_le_right cR _).trans ((min_le_right cP _).trans (min_le_left cV _))) hls.le) (sq_nonneg (N:ℝ)))
  have heR' := hepslt.trans_le (min_le_left eR _)
  have heP' := hepslt.trans_le ((min_le_right eR _).trans (min_le_left eP _))
  have heV' := hepslt.trans_le ((min_le_right eR _).trans ((min_le_right eP _).trans (min_le_left eV _)))
  have he1 : eps≤1 := hepslt.le.trans ((min_le_right eR _).trans ((min_le_right eP _).trans (min_le_right eV _)))
  have hc1 : c≤1/4 := (min_le_right cR _).trans ((min_le_right cP _).trans (min_le_right cV _))
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  have hreg := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hs : s≠0 := by
    have hd : ‖s-radialParameter d.theta eps‖≤c := hsd.trans
      ((div_le_self (by positivity) hn2).trans (mul_le_of_le_one_right hc.le (hl.trans hl1)))
    have hncenter : 1≤‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps.le]; linarith
    have hhalf := norm_ge_half_of_near_unit hncenter (show ‖s-radialParameter d.theta eps‖<1/2 by linarith)
    exact norm_pos_iff.mp (by linarith)
  have hroots (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :=
    hroot N eps lamStar lam θ q s hN heps heR' hls hl hl1 hθ.1 hθ.2 hdR
  have hY (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      1-coordinateProduct (deformedPoint f r τ lam θ)≠0 := by
    have hh := (hroots q θ hθ).2.2.2.trans_lt (Real.exp_lt_one_iff.mpr (by nlinarith : -(3*τ/2)*lam<0))
    intro hz
    rw [← sub_eq_zero.mp hz,norm_one] at hh
    exact lt_irrefl _ hh
  have hZ (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))≠0 := by
    have hh := (hroots q θ hθ).2.2.1.trans_lt (Real.exp_lt_one_iff.mpr (by nlinarith : -aR*lam<0))
    intro hz
    rw [← sub_eq_zero.mp hz,norm_one] at hh
    exact lt_irrefl _ hh
  have hpoint (q : Fin N) (θ : Fin N → ℝ)
      (hθ : θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q)) :
      ‖continuedNamedCurrentDensity f r τ lam s q θ‖≤
        ((N.factorial:ℝ)⁻¹*(2*M/G/lam^2)*D^N*Real.exp (-κ*(N:ℝ)^2))*
          (∏ i, selectedOneBodyBound d.thetaB η C eps (θ i)) := by
    have hnumer := current_actual_inverse_numerator hN f d.c₀_pos.le hτ.le heps.le he1 hc.le hc1
      hls.le hl hl1 hreg.p_nonneg (fun x => (thresholdStep_range _ _ _).2) hreg.m_nonneg hreg.m_le_one θ hsd
    have hgap := current_global_denominator_lower haR (by positivity : 0<3*τ/2) hlam.le hl1
      (hroots q θ hθ).2.2.1 (hroots q θ hθ).2.2.2
    exact continuedNamedCurrentDensity_complete_bound f r τ lam s q θ _
      (by dsimp [A,E]; positivity) hPpos.le hG hlam hJ.le (Real.exp_pos _).le hM.le
      hnumer hgap (hpair N eps lamStar lam θ q s hN heps heP' hls hl hl1 hθ.1 hθ.2 hdP)
      (fun _ => selectedOneBodyBound_nonneg hC.le)
      (hvertex N eps lamStar lam θ q s hN heps heV' hls hl hl1 hθ.1 hθ.2 hdV)
      (fun i => (current_y_norm_envelope (by omega) f d.c₀_pos.le hτ.le heps.le he1 hlam.le hl1
        hreg.p_nonneg (fun x => (thresholdStep_range _ _ _).2) hreg.m_nonneg hreg.m_le_one θ i).1)
      (hjac N (by omega) lam hlam.le hl1 θ) (hmult N q θ)
  have hint := continuedCurrentSlice_norm_le_onebody N f (Real.exp_pos _).ne' τ lam
    hreg.p_smooth hreg.m_smooth hreg.a_smooth hs d.thetaB_pos.le
    (by linarith [d.thetaB_lt,Real.pi_pos]) hC.le heps (by positivity)
    (fun q θ hθ => (hroots q θ hθ).2.1) hY hZ hpoint
  have hnf : (N:ℝ)*(N.factorial:ℝ)⁻¹≤1 := by
    rw [← div_eq_mul_inv]
    apply (div_le_one (by exact_mod_cast Nat.factorial_pos N)).mpr
    exact_mod_cast Nat.self_le_factorial N
  calc
    _ ≤ (N:ℝ)*((N.factorial:ℝ)⁻¹*(2*M/G/lam^2)*D^N*Real.exp (-κ*(N:ℝ)^2))*L^N := hint
    _ = ((N:ℝ)*(N.factorial:ℝ)⁻¹)*((2*M/G/lam^2)*(D*L)^N*Real.exp (-κ*(N:ℝ)^2)) := by dsimp only [D]; simp only [mul_pow]; ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hnf

end
end IsingBulk.Tail
