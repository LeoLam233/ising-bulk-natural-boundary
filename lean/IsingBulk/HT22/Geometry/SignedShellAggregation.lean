import IsingBulk.HT22.Geometry.SignedActualShell

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators ENNReal

/-- Finite means and named extrema are actually counted inside the
nonnegative integral; the final dyadic sum is the complete infinite sum. -/
theorem signedRightRegion_lintegral_geometric {n : ℕ} (hn : 0<n)
    (η : ℝ) (hη : |η|≤Real.pi) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (f : (Fin n → ℝ) → ℝ≥0∞) {K : ℝ} (hK : 0≤K)
    (hb : ∀ m : ℕ,∀ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∀ i a : Fin (n+1),
      (∫⁻ θ in signedRightShell η d B δB (preferredDyadicRadius m) l.1 i a,f θ)≤
        ENNReal.ofReal (K*(1/2:ℝ)^m)) :
    (∫⁻ θ in signedRightRegion η d B δB,f θ)≤ENNReal.ofReal (6*((n+1:ℕ):ℝ)^3*K) := by
  let L := ((preferredMeanIndices (n+1)).card:ℝ)*((n+1:ℕ):ℝ)*((n+1:ℕ):ℝ)
  have hL : 0≤L := by dsimp [L]; positivity
  have hterm (m : ℕ) :
      (∑ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∑ i : Fin (n+1),∑ a : Fin (n+1),
        ∫⁻ θ in signedRightShell η d B δB (preferredDyadicRadius m) l.1 i a,f θ)≤
      ENNReal.ofReal (L*K*(1/2:ℝ)^m) := by
    calc
      _ ≤ ∑ _l : {l : ℤ // l∈preferredMeanIndices (n+1)},∑ _i : Fin (n+1),∑ _a : Fin (n+1),
          ENNReal.ofReal (K*(1/2:ℝ)^m) := by
        apply Finset.sum_le_sum
        intro l _
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum (fun a _ => hb m l i a)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul]
        have hLc : ENNReal.ofReal L=((preferredMeanIndices (n+1)).card:ℝ≥0∞)*((n+1:ℕ):ℝ≥0∞)*((n+1:ℕ):ℝ≥0∞) := by
          dsimp [L]
          rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
          simp only [ENNReal.ofReal_natCast]
        rw [show L*K*(1/2:ℝ)^m=L*(K*(1/2:ℝ)^m) by ring,ENNReal.ofReal_mul hL,hLc]
        ring
  have hsum : Summable (fun m : ℕ => L*K*(1/2:ℝ)^m) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left (L*K)
  have hgeo : (∑' m : ℕ,(1/2:ℝ)^m)=2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]
    norm_num
  have hcount : ((preferredMeanIndices (n+1)).card:ℝ)≤3*((n+1:ℕ):ℝ) := by
    exact_mod_cast preferredMeanIndices_card_le (by omega : 0<n+1)
  calc
    _ ≤ ∑' m : ℕ,ENNReal.ofReal (L*K*(1/2:ℝ)^m) :=
      (signedRightRegion_lintegral_le_shells hn η d B hδB hη f).trans (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (L*K*2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum,tsum_mul_left,hgeo]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_right hcount (by positivity : 0≤((n+1:ℕ):ℝ)^2*K)])


end
end IsingBulk.HT22.Geometry
