import IsingBulk.Tail.SelectedFDerivativeBound

/-! The actual selected F sector is smaller than every epsilon power above
any positive logarithmic even-index cutoff. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Set
open scoped Topology

def selectedDerivativeTail (d : LocalBranchData) (η α τ : ℝ) (j : ℕ) (κ eps : ℝ) : ℝ :=
  ∑' n : ℕ, if 0<n ∧ κ*(-Real.log eps) ≤ (n:ℝ) then
    ‖iteratedDeriv j (selectedIntegral (2*n) (constructedSelector d.thetaB η α)
      (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖ else 0

theorem selectedDerivativeTail_nonneg (d : LocalBranchData) (η α τ : ℝ) (j : ℕ) (κ eps : ℝ) :
    0 ≤ selectedDerivativeTail d η α τ j κ eps := by
  apply tsum_nonneg
  intro n
  split_ifs <;> positivity

/-- Source cutoff constants precede all derivative orders and target powers. -/
theorem selected_actual_epsilon_tail (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∀ (j : ℕ) (κ Q : ℝ), 0 < κ → 0 ≤ Q →
          Tendsto (fun eps : ℝ => selectedDerivativeTail d η α τ j κ eps / eps^Q)
            (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨η₀,τ₀,hη₀,hτ₀,hmain⟩ := selected_actual_derivative_factorial_bound d hcsmall
  refine ⟨η₀,τ₀,hη₀,hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt j κ Q hκ hQ
  obtain ⟨c,e,C,K,a,hc,he,hC,hK,ha,hbound⟩ := hmain η α τ hη hηlt hα hαsmall hτ hτlt
  let A := (j.factorial:ℝ)*c⁻¹^j*K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht := (selected_factorial_epsilon_tail hC.le (by positivity : 0≤(4*a)⁻¹) hκ hQ j).const_mul A
  simp only [mul_zero] at ht
  apply squeeze_zero' (g := fun eps : ℝ => A*((Real.exp ((4*a)⁻¹*Real.log (1-Real.log eps)^2)*
    (∑' n : ℕ, if κ*(-Real.log eps) ≤ (n:ℝ) then selectedFactorialEnvelope C j n else 0))/eps^Q)) ?_ ?_ ht
  · filter_upwards [self_mem_nhdsWithin] with eps heps
    exact div_nonneg (selectedDerivativeTail_nonneg _ _ _ _ _ _ _) (Real.rpow_nonneg (le_of_lt heps) _)
  · have hsmall : ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < min e 1 :=
      (eventually_lt_nhds (lt_min he zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hsmall] with eps heps hepssmall
    have heps : 0 < eps := heps
    have hepsE := hepssmall.trans_le (min_le_left _ _)
    have heps1 := hepssmall.le.trans (min_le_right _ _)
    have hlog : Real.log eps ≤ 0 := Real.log_nonpos heps.le heps1
    have hL : 1+|Real.log eps| ≤ 1-Real.log eps := by rw [abs_of_nonpos hlog]; rfl
    let G := Real.exp ((4*a)⁻¹*Real.log (1-Real.log eps)^2)
    have hG : 0 ≤ G := (Real.exp_pos _).le
    let v := fun n : ℕ => if κ*(-Real.log eps) ≤ (n:ℝ) then selectedFactorialEnvelope C j n else 0
    have hv0 : ∀ n, 0 ≤ v n := by intro n; dsimp [v]; split_ifs <;> positivity [selectedFactorialEnvelope_nonneg hC.le j n]
    have hvs : Summable v := Summable.of_nonneg_of_le hv0 (fun n => by
      dsimp [v]; split_ifs
      · exact le_rfl
      · exact selectedFactorialEnvelope_nonneg hC.le j n) (selected_factorial_series_summable hC.le j)
    have hmajor (n : ℕ) :
        (if 0<n ∧ κ*(-Real.log eps) ≤ (n:ℝ) then
          ‖iteratedDeriv j (selectedIntegral (2*n) (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖ else 0) ≤ A*G*v n := by
      by_cases hn : 0<n ∧ κ*(-Real.log eps) ≤ (n:ℝ)
      · simp only [hn,ite_true,v,and_self]
        have hh := hbound j n eps (1-Real.log eps) hn.1 heps hepsE hL
        have hGe : G=Real.exp (Real.log (1-Real.log eps)^2/(4*a)) := by
          dsimp [G]
          congr 1
          ring
        simpa only [hGe,A] using hh
      · simp only [hn,ite_false]
        exact mul_nonneg (mul_nonneg hA hG) (hv0 n)
    have hus := Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hmajor (hvs.mul_left (A*G))
    have htail : selectedDerivativeTail d η α τ j κ eps ≤ A*G*(∑' n,v n) := by
      exact (Summable.tsum_le_tsum hmajor hus (hvs.mul_left (A*G))).trans_eq (tsum_mul_left)
    have hh := div_le_div_of_nonneg_right htail (Real.rpow_nonneg heps.le Q)
    convert hh using 1
    dsimp [G,v]
    ring

end
end IsingBulk.Tail
