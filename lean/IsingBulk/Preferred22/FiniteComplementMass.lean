import IsingBulk.Preferred22.ActualShellTheorem
import IsingBulk.Preferred22.FiniteRightMass
import IsingBulk.Preferred22.SmallShellMass

/-! The genuine finite-complement mass away from full equality. No large-N
power condition is used: the actual dyadic shells are a finite prefix on
this region. This applies to every even N>=2 and every fixed derivative order. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff

theorem preferredRightShell_diameter_upper {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB r : ℝ} (hr : 0<r) {l : ℤ}
    {i a : Fin (n+1)} {x : Fin n → ℝ} (hx : x∈preferredRightShell d B δB r l i a) :
    preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles x))≤2*r := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [(hx.2.2.2.1 u).1,(hx.2.2.2.1 u).2,
    (hx.2.2.2.1 v).1,(hx.2.2.2.1 v).2,hx.2.2.2.2.2]

def preferredRightAwayMassIntegrand {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (η rcut : ℝ → ℝ) (j : ℕ) (ε ρ : ℝ) (θ : Fin n → ℝ) : ℝ≥0∞ :=
  if ρ≤preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles θ)) then
    ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖
  else 0

/-- Source q28 yields true actual finite-particle mass away from equality,
with no finite-Vandermonde premise and no restriction relating N and j. -/
theorem preferred_right_away_region_bound_of_shells (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (hδB : δB<B.delta)
    (η rcut : ℝ → ℝ) (k : ℕ)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ η rcut k) :
    ∀n : ℕ,2≤n+1→Even (n+1)→∀j : ℕ,j≤k→∀ρ : ℝ,0<ρ→
    ∃A : ℝ,0<A ∧ ∀ε : ℝ,0<ε→ε<ε₀→
      (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightAwayMassIntegrand d B τ η rcut j ε ρ θ)≤ENNReal.ofReal (A*(1+|Real.log ε|)) := by
  intro n hN hEven j hj ρ hρ
  obtain ⟨C,J,hC,hshell⟩ := hq28 j hj
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp
    (preferredDyadicRadius_tendsto_zero.eventually (gt_mem_nhds (half_pos hρ)))
  let E := shellOrderEnvelope C J (n+1)
  have hE : 0≤E := by dsimp [E,shellOrderEnvelope]; positivity
  obtain ⟨L,hL,hpow⟩ := preferred_dyadic_two_power_envelope
    (q:=shellExponent (n+1) j) (Q:=1) hE zero_lt_one le_rfl m₀
  refine ⟨6*((n+1:ℕ):ℝ)^3*L,by positivity,?_⟩
  intro ε hε hεr
  let H := 1+|Real.log ε|
  have hH : 0≤H := by dsimp [H]; positivity
  have hb := preferredRightRegion_lintegral_geometric (by omega : 0<n) d B hδB
    (preferredRightAwayMassIntegrand d B τ η rcut j ε ρ)
    (mul_nonneg hL.le hH) ?_
  · simpa only [H,mul_assoc] using hb
  intro m l i a
  by_cases hm : m<m₀
  · have hdom : (∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a,
        preferredRightAwayMassIntegrand d B τ η rcut j ε ρ θ)≤
        ∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a,
          ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
            (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖ := by
      apply lintegral_mono
      intro θ
      unfold preferredRightAwayMassIntegrand
      split_ifs <;> simp
    have hr := preferredDyadicRadius_pos m
    obtain ⟨hi,hmass⟩ := hshell n hN hEven ε (preferredDyadicRadius m) hε hεr hr l.1 i a
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    change ENNReal.ofReal (preferredRightShellMass d B δB τ η rcut j ε (preferredDyadicRadius m) l.1 i a)=_ at he
    rw [←he] at hdom
    apply hdom.trans
    apply ENNReal.ofReal_le_ofReal
    have hc := every_diameter_shell_comparison hr
      (preferredShellScale_ge_diameter d (n+1) l.1 (preferredDyadicRadius m) hε.le) hN j
    rw [←shell_order_envelope_eq_rpow C J (n+1) (by omega)] at hmass
    calc
      _ ≤ E*(preferredDyadicRadius m)^(shellExponent (n+1) j)*H :=
        hmass.trans (by simpa only [E,H,mul_assoc] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hE) hH)
      _ ≤ (L*(1/2:ℝ)^m)*H := mul_le_mul_of_nonneg_right ((hpow m).1 hm) hH
      _ = _ := by ring
  · have hsmall := hm₀ m (Nat.le_of_not_gt hm)
    have hzero (θ : Fin n → ℝ) (hθ : θ∈preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a) :
        preferredRightAwayMassIntegrand d B τ η rcut j ε ρ θ=0 := by
      unfold preferredRightAwayMassIntegrand
      apply ite_eq_right
      have hd := preferredRightShell_diameter_upper d B (preferredDyadicRadius_pos m) hθ
      linarith
    have hmeas : MeasurableSet (preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a) := by
      rw [preferredRightShell_eq_linear d B hδB]
      exact (preferredLinearRightShell_isClosed d B δB (preferredDyadicRadius m) l.1 i a).measurableSet
    rw [setLIntegral_congr_fun hmeas hzero,lintegral_zero]
    exact bot_le

/-- Exact full angular-box support conversion also retains arbitrary
diameter exclusions after transport. -/
theorem preferredRightAwayMass_lintegral_eq_region {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (ε ρ : ℝ) :
    (∫⁻ θ in angularBox n,preferredRightAwayMassIntegrand d B τ preferredPopulationCutoff rcut j ε ρ θ)=
    ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      preferredRightAwayMassIntegrand d B τ preferredPopulationCutoff rcut j ε ρ θ := by
  let f := preferredRightAwayMassIntegrand (n:=n) d B τ preferredPopulationCutoff rcut j ε ρ
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hsupp : Function.support ((angularBox n).indicator f)⊆preferredRightRegion d B δB := by
    intro θ hθ
    by_contra hn
    by_cases hb : θ∈angularBox n
    · have hz := preferredTransportedDensity_right_support d B τ rcut hcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) _
        (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
        (by intro hh; exact hn ⟨hb,hh⟩)
      have hf : f θ=0 := by
        dsimp [f,preferredRightAwayMassIntegrand]
        simp only [hz,norm_zero,ENNReal.ofReal_zero,ite_self]
      exact hθ (by rw [Set.indicator_of_mem hb,hf])
    · exact hθ (Set.indicator_of_notMem hb _)
  apply le_antisymm
  · calc
      _ = ∫⁻ θ,(angularBox n).indicator f θ := (lintegral_indicator hbox f).symm
      _ = ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,(angularBox n).indicator f θ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)
  · exact lintegral_mono_set (fun θ hθ => hθ.1)

/-- Actual P9 coarse-region mass. The physical regime precedes every finite
particle/derivative order; equality radius is chosen only in the final integral. -/
theorem preferred_actual_right_away_equality_mass (d : PreferredBranchData) :
    ∃cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀B : PreferredCoareaBump d,B.delta<cap→
    ∃δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
    ∀δB : ℝ,0<δB→δB≤δ₀→∀τ : ℝ,0≤τ→τ<τ₀→
    ∀rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut→
    ∀n : ℕ,2≤n+1→Even (n+1)→∀j : ℕ,∀ρ : ℝ,0<ρ→
    ∃A : ℝ,0<A ∧ ∀ε : ℝ,0<ε→ε<ε₀→
      (∫⁻ θ in angularBox n,
        preferredRightAwayMassIntegrand d B τ preferredPopulationCutoff rcut j ε ρ θ)≤
        ENNReal.ofReal (A*(1+|Real.log ε|)) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := preferred_actual_all_diameter_shell_bound d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,hq⟩ := hsource B hB
  refine ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,?_⟩
  intro δB hδB hδB₀ τ hτ hτr rcut hcut n hN hEven j ρ hρ
  have hs := hq δB hδB hδB₀ rcut hcut.2.2.1 hcut.2.2.2.1 τ hτ hτr j
  obtain ⟨A,hA,hbound⟩ := preferred_right_away_region_bound_of_shells d B hcut.2.1
    preferredPopulationCutoff rcut j hs n hN hEven j le_rfl ρ hρ
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  rw [preferredRightAwayMass_lintegral_eq_region d B τ rcut hcut]
  exact hbound ε hε hεr

end
end IsingBulk.Preferred22
