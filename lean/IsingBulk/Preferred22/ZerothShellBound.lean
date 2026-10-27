import IsingBulk.Preferred22.ZerothSourceBound
import IsingBulk.Preferred22.ShellIntegration
import IsingBulk.Preferred22.ShellGeometry
import IsingBulk.Preferred22.BumpChoice
import IsingBulk.Preferred22.RightCutoff

/-! An actual, unconditional j=0 shell bound. The periodic bumps and both
localization cutoffs are explicit; the full normalized physical density and
original one-sided lift occur in the theorem. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ENNReal

/-- The complete physical untransported right-shell estimate. This closes
j=0 on every positive diameter, with no pointwise density, shell or tail
estimate as a premise. Its factored form displays separately the actual
factorial determinant decay and the genuine constrained-coarea measure. -/
theorem preferred_zeroth_right_shell_lintegral (d : PreferredBranchData) :
    ∃ B : PreferredCoareaBump d,∃ A C D ε₀ τ₀ δB : ℝ,
      0<A ∧ 0<C ∧ 0<D ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      PreferredRightCutoffData d B δB (preferredRightCutoff d δB) ∧
      ∀ n : ℕ,∀ ε τ r : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r →
      ∀ l : ℤ,∀ i j : Fin (n+2),
      (∫⁻ x in preferredRightShell d B δB r l i j,
        ENNReal.ofReal ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m
          (preferredRightCutoff d δB) 0 (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredLiftedAngles B.delta (constrainedAngles x))‖) ≤
        ENNReal.ofReal (2*(D/Real.sqrt (n+2:ℕ))^(n+2)*
          (r/Real.sqrt (preferredShellScale d (n+2) l r ε))^(n+2)*
          (A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (preferredShellScale d (n+2) l r ε)/r*(1+|Real.log ε|))*
            (32*r/Real.sqrt (preferredShellScale d (n+2) l r ε))^n)) := by
  obtain ⟨cap,hcap,_,hsource⟩ := preferred_zeroth_source_majorant d
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<cap := cappedCanonicalPreferredBump_delta_lt d hcap
  obtain ⟨D,εm,τm,δm,hD,hεm,hτm,hδm,hδmδ,hm⟩ := hsource B hB
  obtain ⟨A,C,εc,τc,δc,hA,hC,hεc,hτc,hδc,_,hc⟩ := preferred_transported_shell_lintegral d B
  let δB := min δm (min δc (preferredRightMargin d B))
  have hδB : 0<δB := lt_min hδm (lt_min hδc (preferredRightMargin_bounds d B).1)
  have hδBm : δB≤δm := min_le_left _ _
  have hδBc : δB≤δc := (min_le_right _ _).trans (min_le_left _ _)
  have hδBr : δB≤preferredRightMargin d B := (min_le_right _ _).trans (min_le_right _ _)
  have hδBδ : δB<B.delta := hδBm.trans_lt hδmδ
  have hcutoff := preferred_right_cutoff_data_of_le d B hδB hδBr
  refine ⟨B,A,C,D,min εm εc,min τm τc,δB,hA,hC,hD,lt_min hεm hεc,
    lt_min hτm hτc,hδB,hδBδ,hcutoff,?_⟩
  intro n ε τ r hε hεr hτ hτr hr l i j
  let T := preferredShellScale d (n+2) l r ε
  let K := 2*(D/Real.sqrt (n+2:ℕ))^(n+2)*(r/Real.sqrt T)^(n+2)
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (x : Fin (n+1) → ℝ) (hx : x∈preferredRightShell d B δB r l i j) :
      ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m
        (preferredRightCutoff d δB) 0 (IsingBulk.Branch.radialParameter d.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAngles x))‖ ≤
      K*preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles x)) := by
    let w := preferredLiftedAngles B.delta (constrainedAngles x)
    have hbox (v : Fin (n+2)) : -δm≤w v+d.b ∧ w v+d.b≤d.b+B.delta := by
      have hv := hx.2.1 v
      change -d.b-δB≤w v ∧ w v≤B.delta at hv
      constructor <;> linarith [hv.1,hv.2]
    have hwindow := preferredRightShell_window d B hx
    have hh := hm (n+2) (by omega) ε τ (preferredShellMean d (n+2) l) r hε
      (hεr.trans_le (min_le_left _ _)) hτ (hτr.trans_le (min_le_left _ _)) hr w hbox hwindow
      preferredPopulationCutoff (preferredRightCutoff d δB)
      preferredPopulationCutoff_bounds (fun _ => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
    simpa only [K,T,w,preferredShellScale] using hh
  have hh := hc n 0 ε τ r δB K hε (hεr.trans_le (min_le_right _ _)) hτ
    (hτr.trans_le (min_le_right _ _)) hr hδB hδBc hK preferredPopulationCutoff
      (preferredRightCutoff d δB) l i j hpoint
  exact hh

end
end IsingBulk.Preferred22
