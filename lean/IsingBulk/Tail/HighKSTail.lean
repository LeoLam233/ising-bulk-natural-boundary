import IsingBulk.Tail.HighKSBound

/-! Actual high K+small-current absolute tail, summed before taking the
radial limit. The upper particle cutoff may be removed entirely. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Set
open scoped Topology

def highKSNormTail (d : LocalBranchData) (η α τ : ℝ) (j : ℕ) (D eps lamStar : ℝ) : ℝ :=
  ∑' N : ℕ, if 2≤N ∧ D*Real.sqrt (-Real.log eps) ≤ (N:ℝ) then
    originalKSNorm N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ j
      (radialParameter d.theta eps) lamStar else 0

theorem gaussian_window_epsilon_ratio {C κ D Q : ℝ} (hC : 0≤C) (hκ : 0<κ) (hD : 0≤D)
    (j : ℕ) (hcost : ((j+2:ℕ):ℝ)-(κ/2)*D^2 < -Q) :
    Tendsto (fun eps : ℝ => eps⁻¹^(j+2)*gaussianWindowTail C κ D (-Real.log eps)/eps^Q)
      (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun eps : ℝ => -Real.log eps) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hh := (gaussian_window_tail_isLittleO hC hκ hD ((j+2:ℕ):ℝ) (-Q) hcost).tendsto_div_nhds_zero.comp ht
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hp : 0<eps := heps
  simp only [Function.comp_def]
  rw [Real.exp_nat_mul,Real.exp_neg,Real.exp_log hp,Real.rpow_def_of_pos hp]
  congr 2
  ring

set_option maxHeartbeats 1500000 in
theorem actual_highKS_epsilon_tail (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∀ (j : ℕ) (Q : ℝ), 0≤Q → ∃ D : ℝ, 0<D ∧ ∀ μ : ℝ, 0≤μ →
          Tendsto (fun eps : ℝ => highKSNormTail d η α τ j D eps (eps^μ)/eps^Q)
            (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨η₀,hη₀,hmain⟩ := actual_highKS_gaussian_bound d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hsetup⟩ := hmain η hη hηlt
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt j Q hQ
  obtain ⟨c,e,K,C,κ,hc,he,hK,hC,hκ,hbound⟩ := hsetup α τ hα hαlt hτ hτlt
  let D := Real.sqrt (2*(((j+2:ℕ):ℝ)+Q+1)/κ)
  have harg : 0 < 2*(((j+2:ℕ):ℝ)+Q+1)/κ := by positivity
  have hD : 0 < D := Real.sqrt_pos.mpr harg
  have hcost : ((j+2:ℕ):ℝ)-(κ/2)*D^2 < -Q := by
    have hsq : D^2=2*(((j+2:ℕ):ℝ)+Q+1)/κ := Real.sq_sqrt harg.le
    have heq : (κ/2)*D^2=((j+2:ℕ):ℝ)+Q+1 := by rw [hsq]; field_simp
    linarith
  refine ⟨D,hD,?_⟩
  intro μ hμ
  let A := (j.factorial:ℝ)*c⁻¹^j*K
  have hA : 0≤A := by dsimp [A]; positivity
  have ht := (gaussian_window_epsilon_ratio hC.le hκ hD.le j hcost).const_mul A
  simp only [mul_zero] at ht
  apply squeeze_zero' (g := fun eps : ℝ => A*(eps⁻¹^(j+2)*gaussianWindowTail C κ D (-Real.log eps)/eps^Q)) ?_ ?_ ht
  · filter_upwards [self_mem_nhdsWithin] with eps heps
    apply div_nonneg _ (Real.rpow_nonneg (le_of_lt heps) _)
    apply tsum_nonneg
    intro N
    split_ifs
    · exact originalKSNorm_nonneg _ _ _ _ _ _ _
    · exact le_rfl
  · have hsmall : ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < min e 1 :=
      (eventually_lt_nhds (lt_min he zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hsmall] with eps heps hepssmall
    have heps : 0<eps := heps
    have heps1 := hepssmall.le.trans (min_le_right _ _)
    have hepsE := hepssmall.trans_le (min_le_left _ _)
    have hl0 : 0≤eps^μ := Real.rpow_nonneg heps.le μ
    have hl1 : eps^μ≤1 := Real.rpow_le_one heps.le heps1 hμ
    let v := fun N : ℕ => if D*Real.sqrt (-Real.log eps) ≤ (N:ℝ) then C^N*Real.exp (-κ*(N:ℝ)^2) else 0
    have hv0 : ∀ N, 0≤v N := by intro N; dsimp [v]; split_ifs <;> positivity
    have hvs : Summable v := Summable.of_nonneg_of_le hv0 (fun N => show v N ≤ C^N*Real.exp (-κ*(N:ℝ)^2) by
      dsimp [v]
      split_ifs
      · exact le_rfl
      · positivity)
      (by simpa only [pow_zero,mul_one] using summable_source_gaussian hC.le hκ 0)
    have hpoint (N : ℕ) :
        (if 2≤N ∧ D*Real.sqrt (-Real.log eps) ≤ (N:ℝ) then
          originalKSNorm N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ j
            (radialParameter d.theta eps) (eps^μ) else 0) ≤ (A*eps⁻¹^(j+2))*v N := by
      by_cases hn : 2≤N ∧ D*Real.sqrt (-Real.log eps) ≤ (N:ℝ)
      · simp only [hn,and_self,ite_true,v]
        have hh := hbound j N eps (eps^μ) hn.1 heps hepsE hl0 hl1
        convert hh using 1
        dsimp [A]
        ring
      · simp only [hn,ite_false]
        exact mul_nonneg (by positivity) (hv0 N)
    have hs := hvs.mul_left (A*eps⁻¹^(j+2))
    have hu := Summable.of_nonneg_of_le (fun N => by split_ifs; exact originalKSNorm_nonneg _ _ _ _ _ _ _; exact le_rfl) hpoint hs
    have ht' : highKSNormTail d η α τ j D eps (eps^μ) ≤ A*eps⁻¹^(j+2)*gaussianWindowTail C κ D (-Real.log eps) :=
      (Summable.tsum_le_tsum hpoint hu hs).trans_eq tsum_mul_left
    have hh := div_le_div_of_nonneg_right ht' (Real.rpow_nonneg heps.le Q)
    convert hh using 1
    ring

set_option maxHeartbeats 1500000 in
theorem actual_highKS_epsilon_tail_finite_j (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∀ (k : ℕ) (Q : ℝ), 0≤Q → ∃ D : ℝ, 0<D ∧ ∀ j : ℕ, j≤k → ∀ μ : ℝ, 0≤μ →
          Tendsto (fun eps : ℝ => highKSNormTail d η α τ j D eps (eps^μ)/eps^Q)
            (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨η₀,hη₀,hmain⟩ := actual_highKS_gaussian_bound d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hsetup⟩ := hmain η hη hηlt
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt k Q hQ
  obtain ⟨c,e,K,C,κ,hc,he,hK,hC,hκ,hbound⟩ := hsetup α τ hα hαlt hτ hτlt
  let D := Real.sqrt (2*(((k+2:ℕ):ℝ)+Q+1)/κ)
  have harg : 0 < 2*(((k+2:ℕ):ℝ)+Q+1)/κ := by positivity
  have hD : 0 < D := Real.sqrt_pos.mpr harg
  have hcostK : ((k+2:ℕ):ℝ)-(κ/2)*D^2 < -Q := by
    have hsq : D^2=2*(((k+2:ℕ):ℝ)+Q+1)/κ := Real.sq_sqrt harg.le
    have heq : (κ/2)*D^2=((k+2:ℕ):ℝ)+Q+1 := by rw [hsq]; field_simp
    linarith
  refine ⟨D,hD,?_⟩
  intro j hj μ hμ
  have hcost : ((j+2:ℕ):ℝ)-(κ/2)*D^2 < -Q := by
    have hjk : ((j+2:ℕ):ℝ)≤((k+2:ℕ):ℝ) := by exact_mod_cast (show j+2≤k+2 by omega)
    linarith
  let A := (j.factorial:ℝ)*c⁻¹^j*K
  have hA : 0≤A := by dsimp [A]; positivity
  have ht := (gaussian_window_epsilon_ratio hC.le hκ hD.le j hcost).const_mul A
  simp only [mul_zero] at ht
  apply squeeze_zero' (g := fun eps : ℝ => A*(eps⁻¹^(j+2)*gaussianWindowTail C κ D (-Real.log eps)/eps^Q)) ?_ ?_ ht
  · filter_upwards [self_mem_nhdsWithin] with eps heps
    apply div_nonneg _ (Real.rpow_nonneg (le_of_lt heps) _)
    apply tsum_nonneg
    intro N
    split_ifs
    · exact originalKSNorm_nonneg _ _ _ _ _ _ _
    · exact le_rfl
  · have hsmall : ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < min e 1 :=
      (eventually_lt_nhds (lt_min he zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hsmall] with eps heps hepssmall
    have heps : 0<eps := heps
    have heps1 := hepssmall.le.trans (min_le_right _ _)
    have hepsE := hepssmall.trans_le (min_le_left _ _)
    have hl0 : 0≤eps^μ := Real.rpow_nonneg heps.le μ
    have hl1 : eps^μ≤1 := Real.rpow_le_one heps.le heps1 hμ
    let v := fun N : ℕ => if D*Real.sqrt (-Real.log eps) ≤ (N:ℝ) then C^N*Real.exp (-κ*(N:ℝ)^2) else 0
    have hv0 : ∀ N, 0≤v N := by intro N; dsimp [v]; split_ifs <;> positivity
    have hvs : Summable v := Summable.of_nonneg_of_le hv0 (fun N => show v N ≤ C^N*Real.exp (-κ*(N:ℝ)^2) by
      dsimp [v]
      split_ifs
      · exact le_rfl
      · positivity)
      (by simpa only [pow_zero,mul_one] using summable_source_gaussian hC.le hκ 0)
    have hpoint (N : ℕ) :
        (if 2≤N ∧ D*Real.sqrt (-Real.log eps) ≤ (N:ℝ) then
          originalKSNorm N (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ j
            (radialParameter d.theta eps) (eps^μ) else 0) ≤ (A*eps⁻¹^(j+2))*v N := by
      by_cases hn : 2≤N ∧ D*Real.sqrt (-Real.log eps) ≤ (N:ℝ)
      · simp only [hn,and_self,ite_true,v]
        have hh := hbound j N eps (eps^μ) hn.1 heps hepsE hl0 hl1
        convert hh using 1
        dsimp [A]
        ring
      · simp only [hn,ite_false]
        exact mul_nonneg (by positivity) (hv0 N)
    have hs := hvs.mul_left (A*eps⁻¹^(j+2))
    have hu := Summable.of_nonneg_of_le (fun N => by split_ifs; exact originalKSNorm_nonneg _ _ _ _ _ _ _; exact le_rfl) hpoint hs
    have ht' : highKSNormTail d η α τ j D eps (eps^μ) ≤ A*eps⁻¹^(j+2)*gaussianWindowTail C κ D (-Real.log eps) :=
      (Summable.tsum_le_tsum hpoint hu hs).trans_eq tsum_mul_left
    have hh := div_le_div_of_nonneg_right ht' (Real.rpow_nonneg heps.le Q)
    convert hh using 1
    ring

end
end IsingBulk.Tail
