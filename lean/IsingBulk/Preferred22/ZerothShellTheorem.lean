import IsingBulk.Preferred22.ZerothShellBound
import IsingBulk.Preferred22.ZerothContinuity
import IsingBulk.Preferred22.ZerothShellPowers

/-! The actual q28 obligation is closed at transport order zero, including
its genuine integrability clause and exact source rpow exponents. Positive
transport orders and the complete differentiated tail remain separate. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ENNReal

/-- A complete nonconditional instance of the manuscript shell obligation at
j=0, on the exact physical density with concrete smooth periodic cutoffs. -/
theorem preferred_actual_zeroth_all_diameter_shell_bound (d : PreferredBranchData) :
    ∃ B : PreferredCoareaBump d,∃ δB τ₀ ε₀ : ℝ,
      0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      PreferredRightCutoffData d B δB (preferredRightCutoff d δB) ∧
      ∀ τ : ℝ,0≤τ → τ<τ₀ →
        PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff (preferredRightCutoff d δB) 0 := by
  obtain ⟨B,A,C,D,ε₀,τ₀,δB,hA,hC,hD,hε₀,hτ₀,hδB,hδBδ,hcutoff,hbound⟩ :=
    preferred_zeroth_right_shell_lintegral d
  obtain ⟨E,hE,hpowers⟩ := zeroth_shell_q28_envelope hA hC hD
  refine ⟨B,δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,hcutoff,?_⟩
  intro τ hτ hτr j hj
  have hj0 : j=0 := Nat.eq_zero_of_le_zero hj
  subst j
  refine ⟨E,1,hE,?_⟩
  intro n hN _hEven ε r hε hεr hr l i a
  cases n with
  | zero => omega
  | succ m =>
    have hi := preferred_zeroth_right_shell_integrable d B hε hτ hδBδ
      preferredPopulationCutoff (preferredRightCutoff d δB)
      preferredPopulationCutoff_smooth.continuous (preferredRightCutoff_smooth d δB).continuous r l i a
    refine ⟨hi.norm,?_⟩
    let T := preferredShellScale d (m+2) l r ε
    let H := 1+|Real.log ε|
    have hT : 0<T := hr.trans_le (preferredShellScale_ge_diameter d (m+2) l r hε.le)
    have hH : 0≤H := by dsimp [H]; positivity
    have hp := hpowers m r T H hr hT hH
    have hl := hbound m ε τ r hε hεr hτ hτr hr l i a
    have hb := hl.trans (ENNReal.ofReal_le_ofReal hp)
    have he : ENNReal.ofReal (preferredRightShellMass d B δB τ preferredPopulationCutoff
        (preferredRightCutoff d δB) 0 ε r l i a) =
        ∫⁻ x in preferredRightShell d B δB r l i a,
          ENNReal.ofReal ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m
            (preferredRightCutoff d δB) 0 (IsingBulk.Branch.radialParameter d.alpha ε)
            (preferredLiftedAngles B.delta (constrainedAngles x))‖ :=
      ofReal_integral_eq_lintegral_ofReal hi.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    rw [← he] at hb
    have hR : 0≤E^(m+2)*((m+2:ℕ):ℝ)^(-((m+2:ℕ):ℝ)/2+1)*
        r^(2*((m+2:ℕ):ℝ)-3)*T^(-((m+2:ℕ):ℝ)+3/2)*H := by positivity
    have hb' := (ENNReal.ofReal_le_ofReal_iff hR).mp hb
    simpa only [Nat.cast_zero,Nat.cast_one,mul_zero,sub_zero] using hb'

end
end IsingBulk.Preferred22
