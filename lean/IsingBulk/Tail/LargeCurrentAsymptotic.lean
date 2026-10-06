import IsingBulk.Tail.LargeCurrentSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Source epsilon-power split and the actual large-current little-o bound.
The angular endpoint width alpha and the split exponent beta stay distinct. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Asymptotics
open scoped Topology

 theorem cutoff_power_littleo_sqrt {β : ℝ} {j : ℕ}
    (hexp : β*((j:ℝ)+1)<1/2) :
    IsLittleO (nhdsWithin 0 (Ioi 0))
      (fun eps : ℝ => ((eps^β)⁻¹)^(j+1)) (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  have he : 0<(-β)*((j:ℝ)+1)+1/2 := by linarith
  refine (isLittleO_iff_tendsto' (f := fun eps : ℝ => ((eps^β)⁻¹)^(j+1))
    (g := fun eps : ℝ => (Real.sqrt eps)⁻¹) ?_).mpr ?_
  · filter_upwards [self_mem_nhdsWithin] with eps heps
    have hs : (Real.sqrt eps)⁻¹≠0 := inv_ne_zero (Real.sqrt_pos.mpr heps).ne'
    exact fun h => False.elim (hs h)
  · have ht : Tendsto (fun eps : ℝ => eps^((-β)*((j:ℝ)+1)+1/2)) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      have hh : Tendsto (fun eps : ℝ => eps^((-β)*((j:ℝ)+1)+1/2))
          (nhdsWithin 0 (Ioi 0)) (𝓝 ((0:ℝ)^((-β)*((j:ℝ)+1)+1/2))) :=
        (Real.continuous_rpow_const he.le).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Real.zero_rpow he.ne'] using hh
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with eps heps
    rw [div_inv_eq_mul,Real.sqrt_eq_rpow,← Real.rpow_neg heps.le]
    rw [← Real.rpow_natCast,← Real.rpow_mul heps.le,← Real.rpow_add heps]
    push_cast
    rfl

 theorem large_current_positive_even_littleo (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ, 0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,
        0<α → α<α₀ → 0<τ → τ<τ₀ →
        ∀ (j : ℕ) (β : ℝ), 0<β → β*((j:ℝ)+1)<1/2 →
          IsLittleO (nhdsWithin 0 (Ioi 0))
            (fun eps : ℝ => ∑' n : ℕ, ‖∫ lam in (eps^β)..1,
              differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB η α)
                (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)‖)
            (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨η₀,hη₀,hsetup⟩ := large_current_positive_even_series d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hnext⟩ := hsetup η hη hηlt
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt j β hβ hexp
  obtain ⟨e,he,hseries⟩ := hnext α τ hα hαlt hτ hτlt
  obtain ⟨C,hC,hbound⟩ := hseries j
  apply IsBigO.trans_isLittleO (g := fun eps : ℝ => ((eps^β)⁻¹)^(j+1)) ?_ (cutoff_power_littleo_sqrt hexp)
  apply isBigO_iff.mpr
  refine ⟨C,?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds he),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with eps heps hepse heps1
  have hl : 0<eps^β := Real.rpow_pos_of_pos heps _
  have hl1 : eps^β≤1 := Real.rpow_le_one heps.le heps1.le hβ.le
  have hh := (hbound eps (eps^β) heps hepse hl hl1).2
  have hnon : 0≤∑' n : ℕ, ‖∫ lam in (eps^β)..1,
      differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)‖ := tsum_nonneg (fun _ => norm_nonneg _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hnon,abs_of_nonneg (by positivity : 0≤((eps^β)⁻¹)^(j+1))] using hh


 theorem source_split_exponent_margin {β : ℝ} {j k : ℕ} (hβ : 0<β)
    (hβsmall : β<1/(2*((k:ℝ)+2))) (hj : j≤k) : β*((j:ℝ)+1)<1/2 := by
  have hden : 0<2*((k:ℝ)+2) := by positivity
  have hh := (lt_div_iff₀ hden).mp hβsmall
  have hj' : (j:ℝ)≤k := by exact_mod_cast hj
  nlinarith

end
end IsingBulk.Tail
