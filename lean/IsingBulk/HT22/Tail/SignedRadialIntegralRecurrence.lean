import IsingBulk.HT22.Tail.SignedRadialIntegralPunctured
import IsingBulk.HT22.Tail.SignedRadialIntegralRegularity
import IsingBulk.HT22.Tail.SignedRadialIntegralCurrent
import IsingBulk.HT22.Tail.PuncturedTransportIoc

/-! Exact new physical punctured radial recurrence on the full signed torus.
All continuity, integrability and tangent Stokes inputs are constructed from
the actual RegularPoint geometry. The true cutoff flux remains explicit. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem punctured_signed_integral_radial_hasDerivAt {n : ℕ}
    (c : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (R : ℝ) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (j : ℕ)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (signedLiftedRadialIntegral (n:=n) c B.delta d.alpha (puncturedDensity σ d B τ R rcut j))
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*
        (signedLiftedIntegral (n:=n) c B.delta (puncturedDensity σ d B τ R rcut (j+1))
          (IsingBulk.Branch.radialParameter d.alpha ε)-
        signedLiftedIntegral (n:=n) c B.delta
          (fun s x => punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j s R x)
          (IsingBulk.Branch.radialParameter d.alpha ε))) ε := by
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let X := fun q : Fin n → ℝ => preferredLiftedAngles B.delta (constrainedAtTotal c q)
  let H := puncturedDensity (N:=n+1) σ d B τ R rcut j
  let G := puncturedDensity (N:=n+1) σ d B τ R rcut (j+1)
  let D : ℂ → (Fin (n+1) → ℝ) → ℂ := fun t x => preferredAngularDivergence (puncturedCurrent σ d B τ R rcut j t) x
  let J : ℂ → (Fin (n+1) → ℝ) → ℂ := fun t x => punctureFlux σ τ preferredPopulationCutoff B.p B.m rcut j t R x
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × (Fin n → ℝ) =>
      (IsingBulk.Branch.radialParameter d.alpha z.1,constrainedAtTotal c z.2)) := by
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
    exact (((hc.comp (contDiff_const.add contDiff_id)).mul contDiff_const).comp contDiff_fst).prodMk
      ((constrainedAtTotal_contDiff c).comp contDiff_snd)
  have hF (u : ℝ) (hu : u∈Ioo 0 ε₀) (q : Fin n → ℝ) : ContDiffAt ℝ ∞
      (fun z : ℝ × (Fin n → ℝ) => H (IsingBulk.Branch.radialParameter d.alpha z.1) (X z.2)) (u,q) := by
    dsimp only [H,X]
    exact (puncturedDensity_and_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut
      (IsingBulk.Branch.radialParameter d.alpha u) R j (hreg u hu) (constrainedAtTotal c q)).1.comp (u,q) hmap.contDiffAt
  have hH (q : Fin n → ℝ) : DifferentiableAt ℂ (fun t => H t (X q)) s :=
    puncturedDensity_parameter_differentiable (by omega) σ hσ d B rcut hcut s R j _
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal c q)) (hreg ε hε _)
  have hC : Continuous (fun q : Fin n → ℝ => deriv (fun t => H t (X q)) s) :=
    signed_parameter_integrand_continuous c B.delta d.alpha ε H (hF ε hε) hH
  have hG : Continuous (fun q : Fin n → ℝ => G s (X q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact ((puncturedDensity_and_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut
      s R (j+1) (hreg ε hε) (constrainedAtTotal c q)).1.comp q
      (contDiffAt_const.prodMk (constrainedAtTotal_contDiff c).contDiffAt)).continuousAt
  have htan : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      (∑ i,angularField τ B.p B.m s x i)=0 :=
    fun x hx hd => angularField_regularPoint_tangent τ B.p B.m s x (hreg ε hε x hx hd)
  have hD : Continuous (fun q : Fin n → ℝ => D s (X q)) :=
    punctured_ambient_divergence_continuous c σ hσ d B rcut hcut s R j (hreg ε hε) htan
  have hrec (q : Fin n → ℝ) : deriv (fun t => H t (X q)) s=G s (X q)+D s (X q)-J s (X q) :=
    punctured_transport_identity_Ioc (by omega) σ hσ d B rcut hcut j ε R (X q)
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal c q)) (hreg ε hε (X q))
  have hJ : Continuous (fun q : Fin n → ℝ => J s (X q)) := by
    have he : (fun q : Fin n → ℝ => J s (X q))=
        fun q => G s (X q)+D s (X q)-deriv (fun t => H t (X q)) s := by
      funext q
      linear_combination hrec q
    rw [he]
    exact (hG.add hD).sub hC
  exact signed_radial_integral_recurrence c B.delta d.alpha H G D J hε hF hH hrec
    (continuous_integrableOn_angularBox hG) (continuous_integrableOn_angularBox hD)
    (continuous_integrableOn_angularBox hJ)
    (punctured_ambient_divergence_integral c σ hσ d B rcut hcut s R j (hreg ε hε) htan)

end
end IsingBulk.HT22.Tail
