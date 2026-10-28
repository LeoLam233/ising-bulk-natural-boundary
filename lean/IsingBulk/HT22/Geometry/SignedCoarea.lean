import IsingBulk.Preferred22.IntegratedCoarea

/-! Signed F001 scalar coarea. The whole occupancy correction and the
3π/8 projection are exactly the existing proved geometric source estimate;
the sign enters solely as a real phase translation. No zero-sum or parity
assumption is imposed on the actual extreme path. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory IsingBulk.Preferred22

def signedActualZ {N : ℕ} (a : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  Complex.exp (-Complex.I*(a:ℂ))*preferredActualZ d B ε τ θ

def signedProjectedPhase {N : ℕ} (a : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (preferredCompactDirection*(preferredTotalPhase d ε τ B.p B.m θ+(a:ℂ))).re

theorem signedActualZ_eq_exp {N : ℕ} (a : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ) (θ : Fin N → ℝ) :
    signedActualZ a d B ε τ θ=Complex.exp (-Complex.I*(preferredTotalPhase d ε τ B.p B.m θ+(a:ℂ))) := by
  rw [signedActualZ,preferredActualZ_eq_exp d B hε hτ,← Complex.exp_add]
  congr 1
  ring

theorem signedProjectedPhase_shift {N : ℕ} (a : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ : ℝ) (θ : Fin N → ℝ) :
    signedProjectedPhase a d B ε τ θ=preferredProjectedPhase d B ε τ θ+
      (preferredCompactDirection*(a:ℂ)).re := by
  simp only [signedProjectedPhase,preferredProjectedPhase,mul_add,Complex.add_re]

theorem signed_extreme_projected_deriv {N : ℕ} (a : ℝ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0<ε) (hτ : 0≤τ)
    (θ : Fin N → ℝ) (i j : Fin N) (t : ℝ) :
    deriv (fun h : ℝ => signedProjectedPhase a d B ε τ (extremeAnglePath θ i j h)) t=
      actualExtremeProjection d B ε τ (extremeAnglePath θ i j t) i j := by
  simp_rw [signedProjectedPhase_shift]
  rw [deriv_add_const]
  exact preferred_extreme_projected_deriv d B hε hτ θ i j t

theorem signed_actual_oblique_kernel (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c ε₀ : ℝ, 0<c ∧ 0<ε₀ ∧ ∀ a : ℝ, ∀ N : ℕ, 0<N → ∀ ε τ : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ≤1 → ∀ θ : Fin N → ℝ,
      ‖1-signedActualZ a d B ε τ θ‖⁻¹ ≤
        obliqueKernelConstant (Real.cos (3*Real.pi/8)) (Real.sin (3*Real.pi/8)) /
        (c*ε+projectedDistance (Real.cos (3*Real.pi/8)) (signedProjectedPhase a d B ε τ θ)) := by
  obtain ⟨c,C,hc,_,hphase⟩ := preferred_actual_phase_control d B
  let ε₀ := min 1 (1/c)
  have hε₀ : 0<ε₀ := by dsimp [ε₀]; positivity
  refine ⟨c,ε₀,hc,hε₀,?_⟩
  intro a N hN ε τ hε hεr hτ hτ1 θ
  have hε1 : ε≤1 := (hεr.trans_le (min_le_left _ _)).le
  have hcε1 : c*ε≤1 := by
    have h := (lt_div_iff₀ hc).mp (hεr.trans_le (min_le_right _ _))
    nlinarith
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  let G := preferredTotalPhase d ε τ B.p B.m θ+(a:ℂ)
  have hfloor : c*ε≤-G.im := by
    have h := (hphase N hN ε τ hε hε1 hτ hτ1 θ).1
    dsimp [G]
    simp only [add_zero]
    nlinarith [mul_nonneg hc.le hε.le]
  have he : (G.re:ℂ)-Complex.I*((-G.im:ℝ):ℂ)=G := by apply Complex.ext <;> simp
  have h := actual_oblique_periodic_kernel (x:=G.re) (a:=-G.im) (θ:=3*Real.pi/8)
    (by rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos]) (mul_pos hc hε) hcε1 hfloor
  rw [he] at h
  simpa only [G,← signedActualZ_eq_exp a d B hε hτ,signedProjectedPhase,preferredCompactDirection] using h

end
end IsingBulk.HT22.Geometry
