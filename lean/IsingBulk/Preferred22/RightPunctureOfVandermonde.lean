import IsingBulk.Preferred22.PunctureFromMass
import IsingBulk.Preferred22.FiniteSmallShellMass
import IsingBulk.Preferred22.FiniteShellOfVandermonde

/-! Exact puncture error and flux for every even order above the first
singular order. The finite full-Vandermonde block and the infinite q28 block
use the same physical contour, cutoff, field and source thresholds. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

/-- Literal complex integrability and uniform value approximation. -/
def PreferredRightPunctureValueControl (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) (rcut : ℝ → ℝ) (n j : ℕ) : Prop :=
    ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      IntegrableOn (fun θ : Fin n → ℝ =>
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))
        (angularBox n) ∧
      ∀ m : ℕ,
      IntegrableOn (fun θ : Fin n → ℝ =>
        (preferredEqualityCutoff (preferredDyadicRadius m) (preferredLiftedAngles B.delta (constrainedAngles θ)):ℂ)*
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))
        (angularBox n) ∧
      ‖(∫ θ : Fin n → ℝ in angularBox n,
        (preferredEqualityCutoff (preferredDyadicRadius m) (preferredLiftedAngles B.delta (constrainedAngles θ)):ℂ)*
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))-
        preferredTransportedIntegral (n := n) .right B.delta τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|)*(1/8:ℝ)^m

/-- Literal absolute physical current, with constant before epsilon and exhaustion. -/
def PreferredRightPunctureFluxControl (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ ε₀ : ℝ) (rcut : ℝ → ℝ) (n j : ℕ) : Prop :=
    ∃ L : ℝ,0<L ∧ ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
    (∫⁻ θ : Fin n → ℝ in angularBox n,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε (preferredDyadicRadius m)
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal (L*(1+|Real.log ε|)*(1/2:ℝ)^m)

/-- Complete actual puncture control, including the distinct finite block.
No integrated transport identity, shell bound, or field premise survives. -/
theorem preferred_complete_right_puncture_control_of_vandermonde (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a)
    (hV : PreferredFullVandermondeSourceBound d) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ Nstar k : ℕ,2≤Nstar → 2*k+2=Nstar^2 →
      ∀ n : ℕ,Nstar+2≤n+1 → Even (n+1) → ∀ j : ℕ,j≤k →
      PreferredRightPunctureValueControl d B τ ε₁ rcut n j ∧
        PreferredRightPunctureFluxControl d B τ ε₁ rcut n j := by
  obtain ⟨cs,hcs,hcsa,hs⟩ := preferred_actual_all_diameter_shell_bound d
  obtain ⟨cf,hcf,_hcfa,hf⟩ := preferred_finite_block_shell_bound_of_full_vandermonde d hp ha hα hV
  obtain ⟨cg,hcg,_hcga,hg⟩ := preferred_actual_all_order_shell_integrable d
  obtain ⟨cv,hcv,_hcva,hv⟩ := preferred_actual_angular_field_bound d
  refine ⟨min cs (min cf (min cg cv)),lt_min hcs (lt_min hcf (lt_min hcg hcv)),
    (min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  have hcaps : B.delta<cs ∧ B.delta<cf ∧ B.delta<cg ∧ B.delta<cv := by
    simpa only [lt_min_iff] using hBcap
  obtain ⟨δs,τs,εs,hδs,hδsδ,hτs,hεs,hq⟩ := hs B hcaps.1
  obtain ⟨δf,τf,εf,hδf,_hδfδ,hτf,hεf,hfinite⟩ := hf B hcaps.2.1
  obtain ⟨δg,τg,εg,hδg,_hδgδ,hτg,hεg,hcomplex⟩ := hg B hcaps.2.2.1
  obtain ⟨Cv,εv,τv,δv,hCv,hεv,hτv,hδv,_hδvδ,hfield⟩ := hv B hcaps.2.2.2
  let δ₀ := min δs (min δf (min δg δv))
  let τ₀ := min τs (min τf (min τg τv))
  let ε₀ := min εs (min εf (min εg εv))
  refine ⟨δ₀,τ₀,ε₀,lt_min hδs (lt_min hδf (lt_min hδg hδv)),
    (min_le_left _ _).trans_lt hδsδ,lt_min hτs (lt_min hτf (lt_min hτg hτv)),
    lt_min hεs (lt_min hεf (lt_min hεg hεv)),?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr hε₁ hε₁₀ rcut hcut Nstar k hNstar hk n hNl hEven j hj
  have hδs' : δB≤δs ∧ δB≤δf ∧ δB≤δg ∧ δB≤δv := by
    simpa only [δ₀,le_min_iff] using hδB₀
  have hτs' : τ<τs ∧ τ<τf ∧ τ<τg ∧ τ<τv := by
    simpa only [τ₀,lt_min_iff] using hτr
  have hεs' : ε₁≤εs ∧ ε₁≤εf ∧ ε₁≤εg ∧ ε₁≤εv := by
    simpa only [ε₀,le_min_iff] using hε₁₀
  have hq28 := (hq δB hδB hδs'.1 rcut hcut.2.2.1 hcut.2.2.2.1 τ hτ hτs'.1 k).mono_epsilon hεs'.1
  have hfb := hfinite δB τ ε₁ hδB hδs'.2.1 hτ hτs'.2.1 hε₁ hεs'.2.1 rcut hcut Nstar k
  have hnorm : ∀ ε : ℝ,0<ε → ε<ε₁ →
      IntegrableOn (fun θ : Fin n → ℝ =>
        ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖)
        (angularBox n) := by
    by_cases hN : 2*k+4<n+1
    · obtain ⟨_C,_J,_hC,hh⟩ := preferred_right_absolute_bound_of_q28 d B rcut hcut k hq28 j hj
      exact fun ε hε hεr => (hh n hN hEven ε hε hεr).1
    · obtain ⟨_A,_hA,hh⟩ := preferred_finite_right_absolute_bound_of_shells d B rcut hcut Nstar k
        hNstar hk hq28 hfb n hNl (Nat.le_of_not_gt hN) hEven j hj
      exact fun ε hε hεr => (hh ε hε hεr).1
  have hsmall : ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₁ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ)≤
      ENNReal.ofReal (A*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
    by_cases hN : 2*k+4<n+1
    · obtain ⟨C,J,hC,hh⟩ := preferred_right_small_mass_of_q28 d B hcut.2.1
        preferredPopulationCutoff rcut k hq28 j hj
      refine ⟨6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope C J (n+1),?_,hh n hN hEven⟩
      unfold shellOrderEnvelope
      positivity
    · exact preferred_finite_right_small_mass_of_shells d B hcut.2.1
        preferredPopulationCutoff rcut Nstar k hNstar hk hq28 hfb n hNl
        (Nat.le_of_not_gt hN) hEven j hj
  obtain ⟨A,hA,hsmall⟩ := hsmall
  constructor
  · apply preferred_right_puncture_error_of_small_mass (by omega : 0<n) d B rcut hcut hA hnorm _ hsmall
    intro ε hε hεr m l i a
    have hi := hcomplex n (by omega) ε τ hε (hεr.trans_le hεs'.2.2.1) hτ hτs'.2.2.1
      preferredPopulationCutoff rcut preferredPopulationCutoff_smooth hcut.2.2.1 j
      (preferredDyadicRadius m) (preferredDyadicRadius_pos m) l.1 i a
    exact hi.mono_set (preferredRightShell_mono_margin d B hδs'.2.2.1 l.1 i a)
  · apply preferred_right_puncture_flux_bound_of_small_mass d B rcut hcut hA hsmall hCv
    intro ε hε hεr θ hθ hdiam i
    apply hfield (n+1) (by omega) ε τ hε (hεr.trans_le hεs'.2.2.2) hτ hτs'.2.2.2 θ _ hdiam i
    intro v
    exact ⟨by linarith [(hθ v).1,hδs'.2.2.2],(hθ v).2⟩

end
end IsingBulk.Preferred22
