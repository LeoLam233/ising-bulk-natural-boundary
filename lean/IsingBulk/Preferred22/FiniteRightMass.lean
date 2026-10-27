import IsingBulk.Preferred22.RightDerivativeTail
import IsingBulk.Preferred22.FiniteShellPowers

/-! Complete finite-particle right mass from its distinct full-Vandermonde
small shells and the actual all-diameter q28 bound for the finite remaining
radii. Every integer mean and every extreme label is integrated and counted. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

theorem preferredDyadicRadius_tendsto_zero :
    Tendsto preferredDyadicRadius atTop (𝓝 (0:ℝ)) := by
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).const_mul Real.pi
  convert hh using 1
  · funext m
    unfold preferredDyadicRadius
    rw [pow_succ]
    ring
  · simp

theorem preferredDyadicRadius_power_general {q : ℝ} (hq : 1≤q) (m : ℕ) :
    (preferredDyadicRadius m)^q≤(2*Real.pi)^q*(1/2:ℝ)^m := by
  have hd := dyadic_shell_le_geometric hq (m+1)
  have hm : (1/2:ℝ)^(m+1)≤(1/2:ℝ)^m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold preferredDyadicRadius
  rw [Real.mul_rpow (by positivity : 0≤2*Real.pi) (by positivity : 0≤(1/2:ℝ)^(m+1))]
  exact mul_le_mul_of_nonneg_left (hd.trans hm) (by positivity)

/-- A finite prefix with arbitrary real exponent and a genuine positive
small-radius power have one complete geometric envelope. -/
theorem preferred_dyadic_two_power_envelope {E D q Q : ℝ}
    (hE : 0≤E) (hD : 0<D) (hQ : 1≤Q) (m₀ : ℕ) :
    ∃ L : ℝ,0<L ∧ ∀ m : ℕ,
      (m<m₀ → E*(preferredDyadicRadius m)^q≤L*(1/2:ℝ)^m) ∧
      (m₀≤m → D*(preferredDyadicRadius m)^Q≤L*(1/2:ℝ)^m) := by
  let P := ∑ m∈Finset.range m₀,E*(preferredDyadicRadius m)^q/(1/2:ℝ)^m
  have hP : 0≤P := Finset.sum_nonneg (fun m _ => by
    have hr := preferredDyadicRadius_pos m
    positivity)
  let L := 1+P+D*(2*Real.pi)^Q
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  intro m
  constructor
  · intro hm
    have hs : E*(preferredDyadicRadius m)^q/(1/2:ℝ)^m≤P :=
      Finset.single_le_sum (f := fun l => E*(preferredDyadicRadius l)^q/(1/2:ℝ)^l)
        (fun l (_ : l∈Finset.range m₀) => by
        have hr := preferredDyadicRadius_pos l
        positivity) (Finset.mem_range.mpr hm)
    have hPL : P≤L := by
      have hterm : 0≤D*(2*Real.pi)^Q := by positivity
      dsimp [L]
      linarith
    exact (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<1/2) m)).mp (hs.trans hPL)
  · intro _hm
    have hDL : D*(2*Real.pi)^Q≤L := by dsimp [L]; linarith
    calc
      _ ≤ D*((2*Real.pi)^Q*(1/2:ℝ)^m) :=
        mul_le_mul_of_nonneg_left (preferredDyadicRadius_power_general hQ m) hD.le
      _ ≤ L*(1/2:ℝ)^m := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDL (by positivity : 0≤(1/2:ℝ)^m)

/-- The complete actual right region in each intermediate particle order
is logarithmically bounded. Both source shell estimates remain explicit,
and no integrated finite-block estimate is assumed. -/
theorem preferred_finite_right_region_bound_of_shells (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (hδB : δB<B.delta)
    (η rcut : ℝ → ℝ) (Nstar k : ℕ) (hNstar : 2≤Nstar) (hk : 2*k+2=Nstar^2)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ η rcut k)
    (hfinite : PreferredFiniteBlockShellBound d B δB τ ε₀ η rcut Nstar k) :
    ∀ n : ℕ,Nstar+2≤n+1 → n+1≤2*k+4 → Even (n+1) →
    ∀ j : ℕ,j≤k → ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
    (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal (A*(1+|Real.log ε|)) := by
  intro n hNl hNu hEven j hj
  obtain ⟨r₀,hr₀,hf⟩ := hfinite
  obtain ⟨D,hD,hsmall⟩ := hf n hNl hNu hEven j hj
  obtain ⟨C,J,hC,hshell⟩ := hq28 j hj
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp
    (preferredDyadicRadius_tendsto_zero.eventually (gt_mem_nhds hr₀))
  let N := n+1
  let E := shellOrderEnvelope C J N
  let Q := (N:ℝ)^2-2*(j:ℝ)-3
  have hE : 0≤E := by dsimp [E,shellOrderEnvelope]; positivity
  have hQ : 1≤Q := le_trans (by norm_num) (higher_order_collision_degree_four hNstar hNl hj hk)
  obtain ⟨L,hL,hpowers⟩ := preferred_dyadic_two_power_envelope
    (q := shellExponent N j) (Q := Q) hE hD hQ m₀
  refine ⟨6*(N:ℝ)^3*L,by dsimp [N]; positivity,?_⟩
  intro ε hε hεr
  let H := 1+|Real.log ε|
  have hH : 0≤H := by dsimp [H]; positivity
  have hbound := preferredRightRegion_lintegral_geometric (by omega : 0<n) d B hδB
    (fun θ => ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖)
    (mul_nonneg hL.le hH) ?_
  · simpa only [N,H,mul_assoc] using hbound
  intro m l i a
  have hr := preferredDyadicRadius_pos m
  obtain ⟨hi,hmass⟩ := hshell n (by omega) hEven ε (preferredDyadicRadius m) hε hεr hr l.1 i a
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  change ENNReal.ofReal (preferredRightShellMass d B δB τ η rcut j ε (preferredDyadicRadius m) l.1 i a)=_ at he
  rw [←he]
  apply ENNReal.ofReal_le_ofReal
  by_cases hm : m<m₀
  · have hc := every_diameter_shell_comparison hr
      (preferredShellScale_ge_diameter d N l.1 (preferredDyadicRadius m) hε.le) (by omega : 2≤N) j
    rw [←shell_order_envelope_eq_rpow C J N (by omega)] at hmass
    calc
      _ ≤ E*(preferredDyadicRadius m)^(shellExponent N j)*H :=
        hmass.trans (by simpa only [E,N,H,mul_assoc] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hE) hH)
      _ ≤ (L*(1/2:ℝ)^m)*H := mul_le_mul_of_nonneg_right ((hpowers m).1 hm) hH
      _ = _ := by ring
  · have hm' : m₀≤m := Nat.le_of_not_gt hm
    calc
      _ ≤ D*(preferredDyadicRadius m)^Q*H := hsmall ε (preferredDyadicRadius m)
        hε hεr hr (hm₀ m hm') l.1 i a
      _ ≤ (L*(1/2:ℝ)^m)*H := mul_le_mul_of_nonneg_right ((hpowers m).2 hm') hH
      _ = _ := by ring

/-- Literal full-Haar finite-block masses, including genuine integrability
and the actual right support, inherit the complete shell estimate. -/
theorem preferred_finite_right_absolute_bound_of_shells (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (Nstar k : ℕ)
    (hNstar : 2≤Nstar) (hk : 2*k+2=Nstar^2)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k)
    (hfinite : PreferredFiniteBlockShellBound d B δB τ ε₀ preferredPopulationCutoff rcut Nstar k) :
    ∀ n : ℕ,Nstar+2≤n+1 → n+1≤2*k+4 → Even (n+1) →
    ∀ j : ℕ,j≤k → ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      IntegrableOn (fun θ : Fin n → ℝ => ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖) (angularBox n) ∧
      preferredRightAbsoluteTransportMass d B τ rcut n j ε≤A*(1+|Real.log ε|) := by
  intro n hNl hNu hEven j hj
  obtain ⟨A,hA,hregion⟩ := preferred_finite_right_region_bound_of_shells d B hcut.2.1
    preferredPopulationCutoff rcut Nstar k hNstar hk hq28 hfinite n hNl hNu hEven j hj
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  let f := fun θ : Fin n → ℝ => ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖
  have hb : (∫⁻ θ in preferredRightRegion d B δB,ENNReal.ofReal (f θ))≤
      ENNReal.ofReal (A*(1+|Real.log ε|)) := hregion ε hε hεr
  have hi : IntegrableOn f (preferredRightRegion d B δB) := by
    apply preferredRightRegion_integrable_of_shells (by omega : 0<n) d B hcut.2.1 f
    · intro m l i a
      obtain ⟨_C,_J,_hC,hh⟩ := hq28 j hj
      exact (hh n (by omega) hEven ε (preferredDyadicRadius m) hε hεr
        (preferredDyadicRadius_pos m) l.1 i a).1
    · have hf : ∀ θ,‖f θ‖=f θ := fun θ => Real.norm_of_nonneg (norm_nonneg _)
      simp_rw [hf]
      exact hb.trans_lt ENNReal.ofReal_lt_top
  have hzero (θ : Fin n → ℝ) (hθ : θ∈angularBox n \ preferredRightRegion d B δB) : f θ=0 := by
    have hh := preferredTransportedDensity_right_support d B τ rcut hcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) _
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
      (by intro hh; exact hθ.2 ⟨hθ.1,hh⟩)
    dsimp [f]
    rw [hh,norm_zero]
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hib : IntegrableOn f (angularBox n) := hi.of_forall_sdiff_eq_zero hbox hzero
  have hfull : (∫⁻ θ in angularBox n,ENNReal.ofReal (f θ))≤
      ENNReal.ofReal (A*(1+|Real.log ε|)) := by
    rw [preferredTransportedNorm_lintegral_eq_rightRegion d B τ rcut hcut j]
    exact hb
  have he := ofReal_integral_eq_lintegral_ofReal hib
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  rw [←he] at hfull
  exact ⟨hib,(ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfull⟩

end
end IsingBulk.Preferred22
