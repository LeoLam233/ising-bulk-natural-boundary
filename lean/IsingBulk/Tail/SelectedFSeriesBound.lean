import IsingBulk.Tail.SelectedFDerivativeBound

/-! The full actual selected-F derivative series, before restriction to any
finite source tail window. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology

theorem selected_actual_derivative_series_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∀ j : ℕ, ∃ e B A : ℝ, 0 < e ∧ 0 < B ∧ 0 < A ∧
        ∀ eps : ℝ, 0 < eps → eps < e →
          Summable (fun n : ℕ => ‖iteratedDeriv j
            (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖) ∧
          (∑' n : ℕ, ‖iteratedDeriv j
            (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖) ≤
            B*Real.exp (A*Real.log (1-Real.log eps)^2) := by
  obtain ⟨η₀,τ₀,hη₀,hτ₀,hmain⟩ := selected_actual_derivative_factorial_bound d hcsmall
  refine ⟨η₀,τ₀,hη₀,hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt j
  obtain ⟨c,e,C,K,a,hc,he,hC,hK,ha,hbound⟩ := hmain η α τ hη hηlt hα hαsmall hτ hτlt
  let A := (j.factorial:ℝ)*c⁻¹^j*K
  let S := ∑' n : ℕ, selectedFactorialEnvelope C j (n+1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hS : 0 ≤ S := tsum_nonneg (fun n => selectedFactorialEnvelope_nonneg hC.le j (n+1))
  refine ⟨min e 1,A*(S+1),(4*a)⁻¹,lt_min he zero_lt_one,by positivity,by positivity,?_⟩
  intro eps heps hepslt
  have hl : Real.log eps ≤ 0 := Real.log_nonpos heps.le (hepslt.le.trans (min_le_right _ _))
  let G := Real.exp ((4*a)⁻¹*Real.log (1-Real.log eps)^2)
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hGe : G=Real.exp (Real.log (1-Real.log eps)^2/(4*a)) := by dsimp [G]; congr 1; ring
  have hpoint (n : ℕ) :
      ‖iteratedDeriv j (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖ ≤
        (A*G)*selectedFactorialEnvelope C j (n+1) := by
    simpa only [hGe,A] using hbound j (n+1) eps (1-Real.log eps) (by omega) heps
      (hepslt.trans_le (min_le_left _ _)) (by rw [abs_of_nonpos hl]; rfl)
  have hs := (selected_positive_even_series_summable hC.le j).mul_left (A*G)
  have hf := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hs
  refine ⟨hf,?_⟩
  have ht := Summable.tsum_le_tsum hpoint hf hs
  rw [tsum_mul_left] at ht
  exact ht.trans (by dsimp [S,G] at *; nlinarith [mul_nonneg hA.le hG])

theorem selected_prefactor_absorption {A B H : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    B*Real.exp (A*Real.log (1+H)^2) ≤
      Real.exp ((A+B/(Real.log 2)^2)*Real.log (2+H)^2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (1+H) := Real.log_nonneg (by linarith)
  have hlogle : Real.log (1+H) ≤ Real.log (2+H) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogtwo : Real.log 2 ≤ Real.log (2+H) := Real.log_le_log (by norm_num) (by linarith)
  have hsq : Real.log (1+H)^2 ≤ Real.log (2+H)^2 := by nlinarith
  have hsq2 : (Real.log 2)^2 ≤ Real.log (2+H)^2 := by nlinarith
  have hBe : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  calc
    _ ≤ Real.exp B*Real.exp (A*Real.log (2+H)^2) :=
      mul_le_mul hBe (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hA)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (B+A*Real.log (2+H)^2) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsq2 (div_nonneg hB (sq_nonneg (Real.log 2)))
      have he : B/(Real.log 2)^2*(Real.log 2)^2=B := by field_simp
      rw [he] at hh
      nlinarith

/-- Manuscript equation reqF, stronger because the full positive-even sum is bounded. -/
theorem selected_actual_full_series_reqF (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∀ j : ℕ, ∃ e C : ℝ, 0 < e ∧ 0 < C ∧
        ∀ eps : ℝ, 0 < eps → eps < e →
          Summable (fun n : ℕ => ‖iteratedDeriv j
            (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖) ∧
          (∑' n : ℕ, ‖iteratedDeriv j
            (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB η α)
              (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖) ≤
            Real.exp (C*Real.log (2-Real.log eps)^2) := by
  obtain ⟨η₀,τ₀,hη₀,hτ₀,hmain⟩ := selected_actual_derivative_series_bound d hcsmall
  refine ⟨η₀,τ₀,hη₀,hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt j
  obtain ⟨e,B,A,he,hB,hA,hb⟩ := hmain η α τ hη hηlt hα hαsmall hτ hτlt j
  refine ⟨min e 1,A+B/(Real.log 2)^2,lt_min he zero_lt_one,by positivity,?_⟩
  intro eps heps hepslt
  obtain ⟨hs,hh⟩ := hb eps heps (hepslt.trans_le (min_le_left _ _))
  refine ⟨hs,hh.trans ?_⟩
  have hl : Real.log eps ≤ 0 := Real.log_nonpos heps.le (hepslt.le.trans (min_le_right _ _))
  simpa only [sub_eq_add_neg] using selected_prefactor_absorption hA.le hB.le (neg_nonneg.mpr hl)


end
end IsingBulk.Tail
