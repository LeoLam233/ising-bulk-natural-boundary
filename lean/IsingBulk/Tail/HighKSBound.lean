import IsingBulk.Tail.OriginalLowerCauchy
import IsingBulk.Tail.OriginalCurrentCauchy
import IsingBulk.Tail.GaussianWindowSum

/-! Source B_N,j is the actual K derivative norm plus the norm of the
already-differentiated small-current integral. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped Topology

def originalKSNorm (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (j : ℕ) (s : ℂ) (lamStar : ℝ) : ℝ :=
  ‖iteratedDeriv j (originalLowerIntegral N f r τ) s‖+
    ‖∫ lam in 0..lamStar,differentiatedCurrentSlice N f r τ lam j s‖

theorem originalKSNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (j : ℕ) (s : ℂ) (lamStar : ℝ) :
    0 ≤ originalKSNorm N f r τ j s lamStar := add_nonneg (norm_nonneg _) (norm_nonneg _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem actual_highKS_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∃ c e K C κ : ℝ, 0 < c ∧ 0 < e ∧ 0 < K ∧ 0 < C ∧ 0 < κ ∧
        ∀ (j N : ℕ) (eps lamStar : ℝ), 2 ≤ N → 0 < eps → eps < e →
          0 ≤ lamStar → lamStar ≤ 1 →
          originalKSNorm N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ j
            (radialParameter d.theta eps) lamStar ≤
            ((j.factorial:ℝ)*c⁻¹^j*K)*C^N*eps⁻¹^(j+2)*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηK,hηK,hKsetup⟩ := original_lower_derivative_gaussian_bound d hcsmall
  obtain ⟨ηS,hηS,hSsetup⟩ := original_current_small_integral_gaussian_bound d hcsmall
  refine ⟨min ηK ηS,lt_min hηK hηS,?_⟩
  intro η hη hηlt
  obtain ⟨αK,cK,eK,CK,KK,kK,hαK,hcK,heK,hCK,hKK,hkK,hKb⟩ := hKsetup η hη (hηlt.trans_le (min_le_left _ _))
  obtain ⟨αS,τ₀,hαS,hτ₀,hSb⟩ := hSsetup η hη (hηlt.trans_le (min_le_right _ _))
  refine ⟨min αK αS,τ₀,lt_min hαK hαS,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  obtain ⟨cS,eS,KS,CS,kS,hcS,heS,hKS,hCS,hkS,hS⟩ := hSb α τ hα
    (hαlt.trans_le (min_le_right _ _)) hτ hτlt
  let c := min cK cS
  let C := max CK CS
  let κ := min kK kS
  have hc : 0 < c := lt_min hcK hcS
  have hC : 0 < C := lt_of_lt_of_le hCK (le_max_left _ _)
  have hκ : 0 < κ := lt_min hkK hkS
  refine ⟨c,min eK eS,KK+KS,C,κ,hc,lt_min heK heS,by positivity,hC,hκ,?_⟩
  intro j N eps lamStar hN heps hepslt hls0 hls1
  have hK := hKb α hα (hαlt.trans_le (min_le_left _ _)) j N eps τ hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ.le
  have hS' := (hS j N eps lamStar (by omega) heps (hepslt.trans_le (min_le_right _ _)) hls0 hls1).2
  have hiK : cK⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hcK hc).mpr (min_le_left _ _)
  have hiS : cS⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hcS hc).mpr (min_le_right _ _)
  have hKm : ((j.factorial:ℝ)*cK⁻¹^j*KK)*CK^N*eps⁻¹^(j+2)*Real.exp (-kK*(N:ℝ)^2) ≤
      ((j.factorial:ℝ)*c⁻¹^j*KK)*C^N*eps⁻¹^(j+2)*Real.exp (-κ*(N:ℝ)^2) := by
    gcongr
    · exact le_max_left _ _
    · exact min_le_left _ _
  have hSm : ((j.factorial:ℝ)*cS⁻¹^j*KS)*CS^N*eps⁻¹^(j+2)*Real.exp (-kS*(N:ℝ)^2) ≤
      ((j.factorial:ℝ)*c⁻¹^j*KS)*C^N*eps⁻¹^(j+2)*Real.exp (-κ*(N:ℝ)^2) := by
    gcongr
    · exact le_max_right _ _
    · exact min_le_right _ _
  exact (add_le_add (hK.trans hKm) (hS'.trans hSm)).trans_eq (by ring)

end
end IsingBulk.Tail
