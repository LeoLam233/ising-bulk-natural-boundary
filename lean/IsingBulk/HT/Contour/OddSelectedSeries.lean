import IsingBulk.HT.Contour.OddSelectedTerm
import IsingBulk.Tail.SelectedFAsymptotic

/-! The entire odd selected derivative series, with no particle cutoff. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Filter Asymptotics
open scoped Topology

/-- The extra single dummy-weight loss is absorbed into the existing
log-squared subpower scale. -/
theorem linear_log_square_absorption {A B L : ℝ} (hB : 0 ≤ B) (hL : 0 < L) :
    B*L*Real.exp (A*Real.log L^2) ≤
      (B*Real.exp 1)*Real.exp ((A+1)*Real.log L^2) := by
  have hl : L ≤ Real.exp (1+Real.log L^2) := by
    calc
      L = Real.exp (Real.log L) := (Real.exp_log hL).symm
      _ ≤ Real.exp (1+Real.log L^2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (Real.log L-(1/2:ℝ))]
  calc
    _ ≤ B*Real.exp (1+Real.log L^2)*Real.exp (A*Real.log L^2) := by gcongr
    _ = _ := by
      simp only [mul_assoc, ← Real.exp_add]
      congr 1
      ring

/-- HT-1.0 equation reqF for the full odd sequence N=2n+1. -/
theorem odd_selected_actual_full_series_reqF (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∀ j : ℕ, ∃ e C : ℝ, 0 < e ∧ 0 < C ∧
        ∀ eps : ℝ, 0 < eps → eps < e →
          Summable (fun n : ℕ => ‖iteratedDeriv j
            (selectedIntegral (2*n+1) (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖) ∧
          (∑' n : ℕ, ‖iteratedDeriv j
            (selectedIntegral (2*n+1) (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖) ≤
            Real.exp (C*Real.log (2-Real.log eps)^2) := by
  obtain ⟨η₀,τ₀,hη₀,hτ₀,hmain⟩ := odd_selected_actual_derivative_factorial_bound d hcsmall
  refine ⟨η₀,τ₀,hη₀,hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt j
  obtain ⟨c,e,C,K,a,hc,he,hC,hK,ha,hbound⟩ := hmain η α τ hη hηlt hα hαsmall hτ hτlt
  let A := (j.factorial:ℝ)*c⁻¹^j*K
  let S := ∑' n : ℕ, oddSelectedEnvelope C j n
  let B := A*(S+1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hS : 0 ≤ S := tsum_nonneg (fun n => oddSelectedEnvelope_nonneg hC.le j n)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨min e 1,(4*a)⁻¹+1+(B*Real.exp 1)/(Real.log 2)^2,
    lt_min he zero_lt_one,by positivity,?_⟩
  intro eps heps hepslt
  have hl : Real.log eps ≤ 0 := Real.log_nonpos heps.le (hepslt.le.trans (min_le_right _ _))
  let L := 1-Real.log eps
  have hL : 0 < L := by dsimp [L]; linarith
  let G := Real.exp ((4*a)⁻¹*Real.log L^2)
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hGe : G = Real.exp (Real.log L^2/(4*a)) := by dsimp [G]; congr 1; ring
  have hpoint (n : ℕ) :
      ‖iteratedDeriv j (selectedIntegral (2*n+1) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖ ≤
        (A*L*G)*oddSelectedEnvelope C j n := by
    simpa only [hGe,A] using hbound j n eps L heps
      (hepslt.trans_le (min_le_left _ _)) (by simpa only [L,abs_of_nonpos hl,sub_eq_add_neg] using le_refl (1-Real.log eps))
  have hs := (odd_selected_factorial_series_summable hC.le j).mul_left (A*L*G)
  have hf := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hs
  refine ⟨hf,?_⟩
  have ht := Summable.tsum_le_tsum hpoint hf hs
  rw [tsum_mul_left] at ht
  have ht' : (A*L*G)*S ≤ B*L*G := by
    dsimp [B]
    nlinarith [mul_nonneg (mul_nonneg hA.le hL.le) hG]
  apply (ht.trans ht').trans
  apply (linear_log_square_absorption hB.le hL (A := (4*a)⁻¹)).trans
  simpa only [L,sub_eq_add_neg] using
    selected_prefactor_absorption (show 0 ≤ (4*a)⁻¹+1 by positivity)
      (show 0 ≤ B*Real.exp 1 by positivity) (neg_nonneg.mpr hl)

/-- The full actual positive-kernel odd F series is little-o at the
inverse-square-root scale used in HT noncancellation. -/
theorem odd_selected_actual_full_series_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 tau0 : ℝ, 0 < eta0 ∧ 0 < tau0 ∧
      ∀ eta alpha tau : ℝ, 0 < eta → eta < eta0 → 0 < alpha → alpha < Real.sin d.thetaB/4 →
        0 < tau → tau < tau0 → ∀ j : ℕ,
          (fun eps : ℝ => ∑' n : ℕ, ‖iteratedDeriv j
            (selectedIntegral (2*n+1) (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖) =o[𝓝[>] 0]
                (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨eta0,tau0,heta0,htau0,hF⟩ := odd_selected_actual_full_series_reqF d hcsmall
  refine ⟨eta0,tau0,heta0,htau0,?_⟩
  intro eta alpha tau heta hetaSmall halpha halphaSmall htau htauSmall j
  obtain ⟨e,C,he,hC,hbound⟩ := hF eta alpha tau heta hetaSmall halpha halphaSmall htau htauSmall j
  have hb : (fun eps : ℝ => ∑' n : ℕ, ‖iteratedDeriv j
      (selectedIntegral (2*n+1) (constructedSelector d.thetaB eta alpha)
        (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖) =O[𝓝[>] 0]
          (fun eps : ℝ => Real.exp (C*Real.log (2-Real.log eps)^2)) := by
    apply IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < e from
        mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he))] with eps heps hsmall
    have hn : 0 ≤ ∑' n : ℕ, ‖iteratedDeriv j
        (selectedIntegral (2*n+1) (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖ := tsum_nonneg (fun _ => norm_nonneg _)
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos (Real.exp_pos _),one_mul] using
      (hbound eps heps hsmall).2
  exact hb.trans_isLittleO (radial_log_square_growth_littleO C)

end
end IsingBulk.HT.Contour
