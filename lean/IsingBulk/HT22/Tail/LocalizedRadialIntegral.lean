import IsingBulk.HT22.Tail.LocalizedLift
import IsingBulk.HT22.Tail.SignedRadialIntegral
namespace IsingBulk.HT22.Tail
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem localized_ambient_divergence {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (σ : ℂ) (hσ : ‖σ‖≤1) (c : ℝ) {τ δB : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin (n+1) → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB (n+1), preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (s : ℂ) (j : ℕ)
    (hreg : ∀x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x → RegularPoint τ B.p B.m s x) :
    Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence
      (localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j s)
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ))) ∧
    (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence
      (localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j s)
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))=0 := by
  let F : (Fin (n+1) → ℝ) → Fin (n+1) → ℂ := localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j s
  have hupperzero : ∀ x v,1/2<B.p (x v) → ∀ i,F x i=0 :=
    fun x v hv i => localizedCurrent_upper_zero σ d B τ rcut W j s x v hv i
  have htan' : ∀ x,(∀ i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) → (∑ i,F x i)=0 :=
    fun x hx => localizedCurrent_tangent σ d B rcut hcut W hzero s j hreg x hx
  have hχ : ContDiff ℝ ∞ (constrainedAtTotal (n:=n) c) := Tail.constrainedAtTotal_contDiff c
  have hF (i : Fin n) : ContDiff ℝ ∞ (fun θ : Fin n → ℝ =>
      F (preferredLiftedAngles B.delta (constrainedAtTotal c θ)) i.castSucc) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact ((localized_density_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut W hW hzero s j hreg
      (constrainedAtTotal c θ)).2 i.castSucc).comp θ (contDiffAt_const.prodMk hχ.contDiffAt)
  have he : (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))=
      fun θ => ∑ i : Fin n,fderiv ℝ
        (fun x : Fin n → ℝ => F (preferredLiftedAngles B.delta (constrainedAtTotal c x)) i.castSucc)
        θ (Pi.single i 1) := by
    funext θ
    symm
    apply Tail.signed_lifted_intrinsic_divergence_point c d B F hupperzero htan' θ
    intro i
    have hc := localizedCurrent_contDiffAt (by omega) σ hσ d B rcut hcut W hW hzero s j hreg
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ))
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal c θ)) i
    exact (hc.comp _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  constructor
  · change Continuous (fun θ : Fin n → ℝ => preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))
    rw [he]
    apply continuous_finsetSum
    intro i _
    exact ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
  · change (∫ θ : Fin n → ℝ in angularBox n,preferredAngularDivergence F
      (preferredLiftedAngles B.delta (constrainedAtTotal c θ)))=0
    rw [he]
    exact Tail.signed_lifted_divergence_integral c B.delta F hF


theorem localized_integral_radial_hasDerivAt {n : ℕ} (c : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ δB ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin (n+1) → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB (n+1), preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (j : ℕ)
    (hreg : ∀ε∈Ioo 0 ε₀,∀x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (signedLiftedRadialIntegral c B.delta d.alpha
      (localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j))
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*signedLiftedIntegral c B.delta
        (localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W (j+1))
        (IsingBulk.Branch.radialParameter d.alpha ε)) ε := by
  let H := localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j
  let G := localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W (j+1)
  let D := fun s x => preferredAngularDivergence (localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j s) x
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hχ := Tail.constrainedAtTotal_contDiff (n:=n) c
  have hrad : ContDiff ℝ ∞ (IsingBulk.Branch.radialParameter d.alpha) := by
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
    exact (hc.comp (contDiff_const.add contDiff_id)).mul contDiff_const
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      (IsingBulk.Branch.radialParameter d.alpha z.1,constrainedAtTotal c z.2)) :=
    (hrad.comp contDiff_fst).prodMk (hχ.comp contDiff_snd)
  have hF : ∀ u∈Ioo 0 ε₀,∀ q : Fin n → ℝ,ContDiffAt ℝ ∞
      (fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter d.alpha z.1)
        (preferredLiftedAngles B.delta (constrainedAtTotal c z.2))) (u,q) := by
    intro u hu q
    exact (localized_density_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut W hW hzero _ j (hreg u hu)
      (constrainedAtTotal c q)).1.comp (u,q) hmap.contDiffAt
  have hH : ∀ q : Fin n → ℝ,DifferentiableAt ℂ
      (fun t => H t (preferredLiftedAngles B.delta (constrainedAtTotal c q))) s := by
    intro q
    exact localizedDensity_parameter_differentiable (by omega) σ hσ d B rcut hcut W hW hzero s j (hreg ε hε) _
      (preferredLiftedAngles_mem_oneSided B.delta _)
  have hD := localized_ambient_divergence d B σ hσ c rcut hcut W hW hzero s j (hreg ε hε)
  have hG : Continuous (fun q : Fin n → ℝ => G s (preferredLiftedAngles B.delta (constrainedAtTotal c q))) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact ((localized_density_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut W hW hzero s (j+1)
      (hreg ε hε) (constrainedAtTotal c q)).1.comp q (contDiffAt_const.prodMk hχ.contDiffAt)).continuousAt
  have hrec : ∀ q : Fin n → ℝ,
      deriv (fun t => H t (preferredLiftedAngles B.delta (constrainedAtTotal c q))) s=
        G s (preferredLiftedAngles B.delta (constrainedAtTotal c q))+
        D s (preferredLiftedAngles B.delta (constrainedAtTotal c q))-(0:ℂ) := by
    intro q
    change _=(_-_) + _ - 0
    exact (sub_add_cancel _ _).symm.trans (sub_zero _).symm
  have hh := Tail.signed_radial_integral_recurrence c B.delta d.alpha H G D (fun _ _ => 0) hε hF hH hrec
    (continuous_integrableOn_angularBox hG) (continuous_integrableOn_angularBox hD.1)
    (continuous_integrableOn_angularBox continuous_const) hD.2
  simpa only [Tail.signedLiftedIntegral,H,G,integral_zero,sub_zero] using hh

end
end IsingBulk.HT22.Tail
