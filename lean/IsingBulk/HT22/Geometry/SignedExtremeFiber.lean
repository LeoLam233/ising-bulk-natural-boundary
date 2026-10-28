import IsingBulk.HT22.Geometry.SignedRightCoarea
import IsingBulk.Preferred22.ExtremeFiberIntegration

/-! Signed actual geometric fiber, using the existing exact arbitrary-total
fiber geometry, interval connectedness, and unchanged Lebesgue measure. -/
namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory IsingBulk.Preferred22

set_option maxHeartbeats 1200000 in
/-- The complete actual physical pair integral on the full geometric
extreme fiber. Empty fibers, all constrained means and all positive diameters
are included. No finite-component assumption is made about a cutoff. -/
theorem signed_geometric_fiber_pair_integral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ η : ℝ, ∀ n : ℕ, ∀ ε τ c r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ → 0 < r →
      ∀ z : Fin n → ℝ,
      (∫ m in extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
          ‖1-signedActualZ η d B ε τ (preferredFiberConfiguration c z m)‖) ≤
        C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|) := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hbound⟩ := signed_right_extreme_integral d B
  refine ⟨2*C,ε₀,τ₀,δB,by positivity,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro η n ε τ c r hε hεr hτ hτr hr z
  let F := extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z
  let t := d.b+c/((n+2:ℕ):ℝ)
  let T := |t|+r+ε
  have hT : 0 < T := by dsimp [T]; positivity
  by_cases hne : F.Nonempty
  · obtain ⟨x,y,hxy,hF⟩ := extremeShellFiber_eq_Icc (c-∑ i,z i) r (-d.b-δB) B.delta z hne
    have hR := hbound η (n+2) (by omega) ε τ hε hεr hτ hτr
      (preferredFiberConfiguration c z 0) 0 (Fin.last (n+1)) x y r (2*T) hxy hr
      (by dsimp [T]; linarith [abs_nonneg t]) (by
        intro m hm
        have hmem : m ∈ F := by
          change m ∈ extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z
          rw [hF]
          exact hm
        have hg := preferredFiberConfiguration_geometry hmem
        have hwin := preferredFiberConfiguration_mean_window d hmem (Fin.last (n+1))
        have hscale : preferredFiberConfiguration c z m (Fin.last (n+1))+d.b+ε ≤ 2*T := by
          dsimp [T,t]
          linarith [hwin.2,le_abs_self (d.b+c/((n+2:ℕ):ℝ)),abs_nonneg (d.b+c/((n+2:ℕ):ℝ))]
        simpa only [← preferredFiberConfiguration_eq_extremePath] using
          And.intro hg.1 (And.intro hg.2.1 (And.intro hg.2.2.1 hscale)))
    have hsqrt : Real.sqrt (2*T) ≤ 2*Real.sqrt T := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have h2 : Real.sqrt (2:ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
      exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg T)
    rw [hF,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hxy]
    calc
      _ ≤ C*((n+2:ℕ):ℝ)*Real.sqrt (2*T)/r*(1+|Real.log ε|) := by
        simpa only [← preferredFiberConfiguration_eq_extremePath] using hR
      _ ≤ C*((n+2:ℕ):ℝ)*(2*Real.sqrt T)/r*(1+|Real.log ε|) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hr.le) (by positivity)
      _ = _ := by dsimp [T,t]; ring
  · have hF : F=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change (∫ m in F, _) ≤ _
    rw [hF,setIntegral_empty]
    positivity

/-- Continuity of the literal physical pair resolvent on every real
constrained path. Strict product attenuation follows from the physical sheet
of any one factor and nonnegative attenuation of all remaining factors. -/
theorem signed_extreme_resolvent_continuous (η : ℝ) {N : ℕ} (hN : 0 < N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {ε τ : ℝ}
    (hε : 0 < ε) (hτ : 0 ≤ τ) (θ : Fin N → ℝ) (i j : Fin N) :
    Continuous (fun t : ℝ =>
      preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j /
        ‖1-signedActualZ η d B ε τ (extremeAnglePath θ i j t)‖) := by
  have hnum : Continuous (fun t : ℝ => preferredExtremePair d B ε τ (extremeAnglePath θ i j t) i j) :=
    ((preferred_extreme_slope_continuous hN d B hε hτ θ i j i).add continuous_const |>.mul
      ((preferred_extreme_slope_continuous hN d B hε hτ θ i j j).add continuous_const)).norm
  have hG : Continuous (fun t : ℝ => preferredTotalPhase d ε τ B.p B.m (extremeAnglePath θ i j t)) :=
    (preferred_extreme_phase_smooth d B hε hτ θ i j).continuous
  have hZ : Continuous (fun t : ℝ => signedActualZ η d B ε τ (extremeAnglePath θ i j t)) := by
    simp_rw [signedActualZ_eq_exp η d B hε hτ]
    fun_prop
  have hden (t : ℝ) : ‖1-signedActualZ η d B ε τ (extremeAnglePath θ i j t)‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    rw [signedActualZ_eq_exp η d B hε hτ]
    apply preferred_phase_denominator_ne_zero
    have hs : 0 < Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
      (by linarith [d.alpha_lt,Real.pi_pos])
    have hW := (mul_pos hε hs).trans_le (preferredActualW_im_lower d B hε.le hτ (extremeAnglePath θ i j t) i)
    have hneg := (IsingBulk.Branch.lowerArccos_sheet_of_upper hW).2.2.2
    have hsum := preferred_single_phase_attenuation_le_total d B hε hτ (extremeAnglePath θ i j t) i
    change (preferredAngularPhase d ε (deformedAngles τ B.p B.m (extremeAnglePath θ i j t) i)).im < 0 at hneg
    simp only [Complex.add_im,Complex.ofReal_im,add_zero]
    linarith
  exact hnum.div ((continuous_const.sub hZ).norm) hden

theorem signed_geometric_fiber_pair_integrable (η : ℝ) {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ)
    (c r lo hi : ℝ) (z : Fin n → ℝ) :
    IntegrableOn (fun m : ℝ =>
      preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
        ‖1-signedActualZ η d B ε τ (preferredFiberConfiguration c z m)‖)
      (extremeShellFiber (c-∑ i,z i) r lo hi z) := by
  have hc := signed_extreme_resolvent_continuous η (by omega : 0 < n+2) d B hε hτ
    (preferredFiberConfiguration c z 0) 0 (Fin.last (n+1))
  have hc' : Continuous (fun m : ℝ =>
      preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
        ‖1-signedActualZ η d B ε τ (preferredFiberConfiguration c z m)‖) := by
    simpa only [← preferredFiberConfiguration_eq_extremePath] using hc
  exact hc'.continuousOn.integrableOn_compact (extremeShellFiber_isCompact _ _ _ _ _)

/-- Nonnegative-integral form for genuine Tonelli assembly of the complete
actual transported density. The finite physical pair integral is proved here,
not supplied as a tail-envelope hypothesis. -/
theorem signed_geometric_fiber_pair_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δB : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δB ∧ δB < B.delta ∧
      ∀ η : ℝ, ∀ n : ℕ, ∀ ε τ c r : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ → 0 < r →
      ∀ z : Fin n → ℝ,
      (∫⁻ m in extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        ENNReal.ofReal (preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
          ‖1-signedActualZ η d B ε τ (preferredFiberConfiguration c z m)‖)) ≤
        ENNReal.ofReal (C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|)) := by
  obtain ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,hbound⟩ := signed_geometric_fiber_pair_integral d B
  refine ⟨C,ε₀,τ₀,δB,hC,hε₀,hτ₀,hδB,hδBδ,?_⟩
  intro η n ε τ c r hε hεr hτ hτr hr z
  rw [← ofReal_integral_eq_lintegral_ofReal
    (signed_geometric_fiber_pair_integrable η d B hε hτ c r (-d.b-δB) B.delta z)
    (Filter.Eventually.of_forall (fun m : ℝ => by unfold preferredExtremePair; positivity))]
  exact ENNReal.ofReal_le_ofReal (hbound η n ε τ c r hε hεr hτ hτr hr z)


end
end IsingBulk.HT22.Geometry
