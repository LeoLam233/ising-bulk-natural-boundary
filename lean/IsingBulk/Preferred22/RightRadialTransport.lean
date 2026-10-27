import IsingBulk.Preferred22.PuncturedRadialIntegral
import IsingBulk.Preferred22.RadialDerivativeLimit
import IsingBulk.Preferred22.RadialIteratedIntegral
import IsingBulk.Preferred22.ActualTangency
import IsingBulk.Preferred22.ActualPunctureFlux
import IsingBulk.Preferred22.RightPunctureApproximation

/-! The actual global right transport identity. Smooth periodic Stokes is
proved at each fixed puncture. Quantitative actual shell mass and current
estimates then pass its radial derivative through the equality exhaustion. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Absolute current estimates control the literal complex flux integral.
This is a numerical consequence of the actual Bochner integral inequality. -/
theorem preferred_puncture_flux_integral_norm {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ)
    (rcut : ℝ → ℝ) (j : ℕ) (R ε L : ℝ) (hL : 0≤L)
    (hbound : (∫⁻ θ : Fin n → ℝ in angularBox n,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε R
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤ENNReal.ofReal L) :
    ‖preferredPunctureFluxIntegral n d B τ rcut j R ε‖≤L := by
  apply (norm_integral_le_lintegral_norm _).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hL)

/-- Quantitative genuine puncture errors imply the radial derivative of
the original full right integral. The hypotheses are the precise outputs
of the separate actual mass, flux, regularity and tangency proofs. -/
theorem preferred_right_radial_hasDerivAt_of_puncture_estimates {n j : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredPhysicalRegularDomain τ B.p B.m)
    (htan : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0)
    (happrox : ∀ l : ℕ,l≤j+1 → ∃ A : ℝ,0<A ∧ ∀ ε∈Ioo 0 ε₀,∀ m : ℕ,
      ‖preferredPuncturedRightIntegral n d B τ rcut l (preferredDyadicRadius m) ε-
        preferredRightRadialIntegral n d B τ rcut l ε‖≤A*(1+|Real.log ε|)*(1/8:ℝ)^m)
    (hflux : ∃ L : ℝ,0<L ∧ ∀ ε∈Ioo 0 ε₀,∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in angularBox n,
        ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε (preferredDyadicRadius m)
          (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
        ENNReal.ofReal (L*(1+|Real.log ε|)*(1/2:ℝ)^m))
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) :
    HasDerivAt (preferredRightRadialIntegral n d B τ rcut j)
      (Complex.exp ((d.alpha:ℂ)*Complex.I)*preferredRightRadialIntegral n d B τ rcut (j+1) ε) ε := by
  obtain ⟨A,hA,hAerror⟩ := happrox j (by omega)
  obtain ⟨C,hC,hCerror⟩ := happrox (j+1) le_rfl
  obtain ⟨L,hL,hLerror⟩ := hflux
  let ζ := Complex.exp ((d.alpha:ℂ)*Complex.I)
  let F := fun m : ℕ => preferredPuncturedRightIntegral n d B τ rcut j (preferredDyadicRadius m)
  let F' := fun m : ℕ => fun t : ℝ => ζ*
    (preferredPuncturedRightIntegral n d B τ rcut (j+1) (preferredDyadicRadius m) t-
      preferredPunctureFluxIntegral n d B τ rcut j (preferredDyadicRadius m) t)
  have hζ : ‖ζ‖=1 := Complex.norm_exp_ofReal_mul_I d.alpha
  have hpow (m : ℕ) : (1/8:ℝ)^m≤(1/2:ℝ)^m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  apply preferred_hasDerivAt_of_log_geometric_approximants F F'
    (preferredRightRadialIntegral n d B τ rcut j)
    (fun t => ζ*preferredRightRadialIntegral n d B τ rcut (j+1) t)
    (ρ := (1/2:ℝ)) (A := A) (B := C+L) (by norm_num) (by norm_num) hA.le (by positivity)
    ?_ ?_ ?_ hε
  · intro m t ht
    exact preferred_punctured_right_integral_hasDerivAt d B rcut hcut (preferredDyadicRadius m) j hreg htan ht
  · intro m t ht
    apply (hAerror t ht m).trans
    exact mul_le_mul_of_nonneg_left (hpow m) (by positivity)
  · intro m t ht
    have hcurrent : ‖preferredPunctureFluxIntegral n d B τ rcut j (preferredDyadicRadius m) t‖≤
        L*(1+|Real.log t|)*(1/2:ℝ)^m :=
      preferred_puncture_flux_integral_norm d B τ rcut j (preferredDyadicRadius m) t _
        (by positivity) (hLerror t ht m)
    have hnext : ‖preferredPuncturedRightIntegral n d B τ rcut (j+1) (preferredDyadicRadius m) t-
        preferredRightRadialIntegral n d B τ rcut (j+1) t‖≤C*(1+|Real.log t|)*(1/2:ℝ)^m :=
      (hCerror t ht m).trans (mul_le_mul_of_nonneg_left (hpow m) (by positivity))
    change ‖ζ*(_-_)-ζ*_‖≤_
    rw [←mul_sub,norm_mul,hζ,one_mul]
    have he :
        preferredPuncturedRightIntegral n d B τ rcut (j+1) (preferredDyadicRadius m) t-
          preferredPunctureFluxIntegral n d B τ rcut j (preferredDyadicRadius m) t-
          preferredRightRadialIntegral n d B τ rcut (j+1) t=
        (preferredPuncturedRightIntegral n d B τ rcut (j+1) (preferredDyadicRadius m) t-
          preferredRightRadialIntegral n d B τ rcut (j+1) t)-
          preferredPunctureFluxIntegral n d B τ rcut j (preferredDyadicRadius m) t := by ring
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hnext hcurrent).trans_eq (by ring))

/-- Complete actual right transport for all large even particle orders.
The same arbitrary sufficiently narrow bump and every smaller right margin
are retained through all choices; one regime precedes all transport orders.
No integral-transport, mass, flux, or differentiated-tail premise remains. -/
theorem preferred_actual_large_right_integral_identity (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ k : ℕ,PreferredLargeRightIntegralIdentity d B τ ε₀ rcut k := by
  obtain ⟨ca,hca,hcaa,ha⟩ := preferred_actual_right_puncture_approximation d
  obtain ⟨cf,hcf,_hcfa,hf⟩ := preferred_actual_puncture_flux_uniform d
  obtain ⟨cg,hcg,_hcga,hg⟩ := preferred_actual_regularDomain d
  obtain ⟨ct,hct,_hcta,ht⟩ := preferred_actual_right_tangency d
  let cap := min ca (min cf (min cg ct))
  refine ⟨cap,lt_min hca (lt_min hcf (lt_min hcg hct)),(min_le_left _ _).trans_lt hcaa,?_⟩
  intro B hBcap
  have hBa : B.delta<ca := hBcap.trans_le (min_le_left _ _)
  have hBf : B.delta<cf := hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hBg : B.delta<cg := hBcap.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hBt : B.delta<ct := hBcap.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨δa,τa,εa,hδa,hδaδ,hτa,hεa,ha'⟩ := ha B hBa
  obtain ⟨δf,τf,εf,hδf,_hδfδ,hτf,hεf,hf'⟩ := hf B hBf
  obtain ⟨δg,τg,εg,hδg,_hδgδ,hτg,hεg,hg'⟩ := hg B hBg
  obtain ⟨δt,τt,εt,hδt,_hδtδ,hτt,hεt,ht'⟩ := ht B hBt
  let δ₀ := min δa (min δf (min δg δt))
  let τ₀ := min τa (min τf (min τg τt))
  let ε₀ := min εa (min εf (min εg εt))
  refine ⟨δ₀,τ₀,ε₀,lt_min hδa (lt_min hδf (lt_min hδg hδt)),
    (min_le_left _ _).trans_lt hδaδ,lt_min hτa (lt_min hτf (lt_min hτg hτt)),
    lt_min hεa (lt_min hεf (lt_min hεg hεt)),?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr k n hN hEven
  have hδBa : δB≤δa := hδB₀.trans (min_le_left _ _)
  have hδBf : δB≤δf := hδB₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδBg : δB≤δg := hδB₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδBt : δB≤δt := hδB₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hτa' : τ<τa := hτr.trans_le (min_le_left _ _)
  have hτf' : τ<τf := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτg' : τ<τg := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτt' : τ<τt := hτr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεa' : ε₀≤εa := min_le_left _ _
  have hεf' : ε₀≤εf := (min_le_right _ _).trans (min_le_left _ _)
  have hεg' : ε₀≤εg := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεt' : ε₀≤εt := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hreg : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredPhysicalRegularDomain τ B.p B.m := by
    intro ε hε x hx hd
    apply hg' (n+1) (by omega) ε τ hε.1 (hε.2.trans_le hεg') hτ hτg' x _ hd
    intro i
    exact ⟨by linarith [(hx i).1],(hx i).2⟩
  have htan : ∀ ε∈Ioo 0 ε₀,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0 := by
    intro ε hε x hx hd
    apply ht' (n+1) (by omega) ε τ hε.1 (hε.2.trans_le hεt') hτ hτt' x _ hd
    intro i
    exact ⟨by linarith [(hx i).1],(hx i).2⟩
  have hderiv : ∀ j : ℕ,j<k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      HasDerivAt (preferredRightRadialIntegral n d B τ rcut j)
        (Complex.exp ((d.alpha:ℂ)*Complex.I)*preferredRightRadialIntegral n d B τ rcut (j+1) ε) ε := by
    intro j hj ε hε
    apply preferred_right_radial_hasDerivAt_of_puncture_estimates d B rcut hcut hreg htan ?_ ?_ hε
    · intro l hl
      obtain ⟨A,hA,herr⟩ := ha' δB hδB hδBa rcut hcut τ hτ hτa' k l n (by omega) hN hEven
      refine ⟨A,hA,?_⟩
      intro e he m
      exact ((herr e he.1 (he.2.trans_le hεa')).2 m).2
    · obtain ⟨L,hL,herr⟩ := hf' δB hδB hδBf rcut hcut τ hτ hτf' k j n (by omega) hN hEven
      exact ⟨L,hL,fun e he m => herr e he.1 (he.2.trans_le hεf') m⟩
  intro j hj ε hε hεr
  exact preferred_right_iterated_integral_of_radial_derivatives n d B hτ rcut
    hcut.2.2.1 hcut.2.2.2.1 k hderiv j hj ε ⟨hε,hεr⟩

end
end IsingBulk.Preferred22
