import IsingBulk.Tail.CompactGuardedLieJets
import IsingBulk.Tail.CompactAllowedDiameter
import IsingBulk.Tail.CompactNearFarIntegral

namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set
open scoped ContDiff

/-- The selected-pair denominator cancels against the retained selected zeros.
Only two full-collision powers per Lie step are lost. -/
theorem compact_guarded_near_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℂ} {x : E} {J M k : ℕ} {ρ d C B K : ℝ} {a : ℤ}
    (h : RealScaledJetBound F x J ρ ((B*(C*d^a)*d^(-(2*M:ℕ):ℤ))*K^k)
      ((2*M:ℕ)-2*(k:ℤ)))
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hρd : ρ ≤ d) (hk : k ≤ M) :
    ‖F x‖ ≤ (B*C*K^k)*d^(a-2*(k:ℤ)) := by
  have he : (B*(C*d^a)*d^(-(2*M:ℕ):ℤ))*K^k=
      (B*C*K^k)*d^(a-(2*M:ℕ)) := by
    rw [zpow_sub₀ hd.ne',zpow_neg]
    ring
  rw [he] at h
  have hh := h.absorb_selected_scale hd hρ hρd (by omega)
  convert hh using 1
  congr 2
  ring

theorem compact_guarded_far_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℂ} {x : E} {J M k : ℕ} {ρ d C B K : ℝ}
    (h : RealScaledJetBound F x J ρ ((B*C*d^(-(2*M:ℕ):ℤ))*K^k)
      ((2*M:ℕ)-2*(k:ℤ)))
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hk : k ≤ M) :
    ‖F x‖ ≤ (B*C*K^k)*d^(-(2*M:ℕ):ℤ) := by
  have hh := h.bound 0 (Nat.zero_le J)
  simp only [norm_iteratedFDeriv_zero,Nat.cast_zero,sub_zero] at hh
  have hp : ρ^((2*M:ℕ)-2*(k:ℤ)) ≤ (1:ℝ) := by
    have hh := zpow_le_zpow_left₀ (show 0 ≤ (2*M:ℕ)-2*(k:ℤ) by omega) hρ hρ1
    simpa only [one_zpow] using hh
  exact (hh.trans (mul_le_of_le_one_right h.nonneg hp)).trans_eq (by ring)

/-- Near and far estimates for an allowed diameter feed the same full-cube
coarea integral. In particular the named current coordinate need not belong
to the pair set. -/
theorem compact_allowed_near_far_pointwise {N m q : ℕ}
    (P : Finset (Fin N × Fin N)) (θ : Fin N → ℝ) {ρ A B L : ℝ}
    (hρ : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hd : 0 < compactAllowedDiameter P θ) {F : ℂ}
    (hnear : compactAllowedDiameter P θ ≤ ρ →
      ‖F‖ ≤ A*compactAllowedDiameter P θ^(m+1)*L)
    (hfar : ρ ≤ compactAllowedDiameter P θ →
      ‖F‖ ≤ B*compactAllowedDiameter P θ^(-(q:ℤ))*L) :
    ‖F‖ ≤ (A*ρ^m+B*ρ^(-(q+1:ℕ):ℤ))*(allBranchExteriorDiameter θ*L) := by
  let d := compactAllowedDiameter P θ
  have hdf := compactAllowedDiameter_le_full P θ
  have hf := allBranchExterior_diameter_nonneg θ
  by_cases hn : d ≤ ρ
  · calc
      ‖F‖ ≤ A*d^(m+1)*L := hnear hn
      _ = (A*d^m)*(d*L) := by rw [pow_succ]; ring
      _ ≤ (A*ρ^m)*(allBranchExteriorDiameter θ*L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hn m) hA)
          (mul_le_mul_of_nonneg_right hdf hL) (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (mul_nonneg hf hL)
  · have hrd : ρ ≤ d := le_of_lt (lt_of_not_ge hn)
    have hp : d^(-(q:ℤ)) ≤ ρ^(-(q+1:ℕ):ℤ)*d := by
      calc
        _ = d^(-(q+1:ℕ):ℤ)*d := by
          conv_rhs => rhs; rw [← zpow_one d]
          rw [← zpow_add₀ hd.ne']
          congr 1
          omega
        _ ≤ _ := mul_le_mul_of_nonneg_right (by
          simp only [zpow_neg,zpow_natCast]
          exact inv_anti₀ (pow_pos hρ _) (pow_le_pow_left₀ hρ.le hrd _)) hd.le
    calc
      ‖F‖ ≤ B*d^(-(q:ℤ))*L := hfar hrd
      _ ≤ B*(ρ^(-(q+1:ℕ):ℤ)*d)*L := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hB) hL
      _ = (B*ρ^(-(q+1:ℕ):ℤ))*(d*L) := by ring
      _ ≤ (B*ρ^(-(q+1:ℕ):ℤ))*(allBranchExteriorDiameter θ*L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdf hL) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (mul_nonneg hf hL)

theorem compact_allowed_near_far_integral {N m q : ℕ}
    (P : Finset (Fin N × Fin N)) {R ρ A B Budget : ℝ}
    (L : (Fin N → ℝ) → ℝ) (F : (Fin N → ℝ) → ℂ)
    (hρ : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : ∀ θ, 0 ≤ L θ)
    (hInt : IntegrableOn (fun θ => allBranchExteriorDiameter θ*L θ)
      (Icc (fun _ => -R) (fun _ => R)))
    (hBudget : (∫ θ in Icc (fun _ => -R) (fun _ => R), allBranchExteriorDiameter θ*L θ) ≤ Budget)
    (hPoint : ∀ᵐ θ ∂volume.restrict (Icc (fun _ => -R) (fun _ => R)),
      0 < compactAllowedDiameter P θ ∧
      (compactAllowedDiameter P θ ≤ ρ → ‖F θ‖ ≤ A*compactAllowedDiameter P θ^(m+1)*L θ) ∧
      (ρ ≤ compactAllowedDiameter P θ → ‖F θ‖ ≤ B*compactAllowedDiameter P θ^(-(q:ℤ))*L θ)) :
    ‖∫ θ in Icc (fun _ => -R) (fun _ => R), F θ‖ ≤
      (A*ρ^m+B*ρ^(-(q+1:ℕ):ℤ))*Budget := by
  have hcoef : 0 ≤ A*ρ^m+B*ρ^(-(q+1:ℕ):ℤ) := by positivity
  calc
    _ ≤ ∫ θ in Icc (fun _ => -R) (fun _ => R),
        (A*ρ^m+B*ρ^(-(q+1:ℕ):ℤ))*(allBranchExteriorDiameter θ*L θ) := by
      apply norm_integral_le_of_norm_le (hInt.const_mul _)
      filter_upwards [hPoint] with θ hθ
      exact compact_allowed_near_far_pointwise P θ hρ hA hB (hL θ) hθ.1 hθ.2.1 hθ.2.2
    _ = (A*ρ^m+B*ρ^(-(q+1:ℕ):ℤ))*(∫ θ in Icc (fun _ => -R) (fun _ => R),
        allBranchExteriorDiameter θ*L θ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hBudget hcoef

end
end IsingBulk.Tail
