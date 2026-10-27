import IsingBulk.Preferred22.SmallShellMass
import IsingBulk.Preferred22.AngularFieldBound
import IsingBulk.Preferred22.EqualityCutoff
import IsingBulk.Preferred22.TransportSupport

/-! Vanishing of the actual smooth equality-puncture current in every
large even particle order. The integrated torus transport identity is not
assumed or claimed by this local flux theorem. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff

theorem preferredEqualityCutoff_bounds {N : ℕ} (R : ℝ) (θ : Fin N → ℝ) :
    0≤preferredEqualityCutoff R θ ∧ preferredEqualityCutoff R θ≤1 :=
  preferredPopulationCutoff_bounds _

theorem preferredEqualityCutoff_one_of_diameter_lt {N : ℕ} {R : ℝ}
    (hR : 0<R) (θ : Fin N → ℝ) (hd : R<preferredAngularDiameter θ) :
    preferredEqualityCutoff R θ=1 := by
  apply preferredPopulationCutoff_one
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  nlinarith [preferredEqualitySize_diameter_sq θ,
    sq_nonneg (preferredAngularDiameter θ-R)]

/-- The actual smooth puncture exhausts every nonequality configuration. -/
theorem preferredEqualityCutoff_eventually_one {N : ℕ} (θ : Fin N → ℝ)
    (hd : 0<preferredAngularDiameter θ) :
    ∀ᶠ m : ℕ in atTop,preferredEqualityCutoff (preferredDyadicRadius m) θ=1 := by
  have ht : Tendsto preferredDyadicRadius atTop (𝓝 (0:ℝ)) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul Real.pi
    convert hh using 1
    · funext m
      unfold preferredDyadicRadius
      rw [pow_succ]
      ring
    · simp
  filter_upwards [ht.eventually (gt_mem_nhds hd)] with m hm
  exact preferredEqualityCutoff_one_of_diameter_lt (preferredDyadicRadius_pos m) θ hm

/-- The full actual right region is a countable union of genuine affine
closed boxes; this supplies measurability without treating a modulo lift
as globally continuous. -/
theorem preferredRightRegion_measurable {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta) :
    MeasurableSet (preferredRightRegion (n := n) d B δB) := by
  let A := fun l : ℤ => {θ : Fin n → ℝ | ∀ i,
    constrainedAtTotal (2*Real.pi*(l:ℝ)) θ i∈Icc (-d.b-δB) B.delta}
  have he : preferredRightRegion (n := n) d B δB=⋃ l : ℤ,A l := by
    ext θ
    constructor
    · intro hθ
      obtain ⟨l,hl⟩ := preferredLiftedAngles_integer_mean B.delta θ
      have hrep := preferred_lift_eq_affine_on_right d B hδB θ hθ.1 hθ.2 hl
      apply mem_iUnion.mpr
      refine ⟨l,?_⟩
      simpa only [A,Set.mem_ofPred_eq,hrep] using hθ.2
    · intro hθ
      obtain ⟨l,hl⟩ := mem_iUnion.mp hθ
      obtain ⟨hb,hrep⟩ := preferred_lift_eq_affine_from_right d B hδB l θ hl
      exact ⟨hb,by simpa only [A,Set.mem_ofPred_eq,hrep] using hl⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have heA : A l=⋂ i : Fin (n+1),{θ : Fin n → ℝ |
      constrainedAtTotal (2*Real.pi*(l:ℝ)) θ i∈Icc (-d.b-δB) B.delta} := by ext θ; simp [A]
  rw [heA]
  apply MeasurableSet.iInter
  intro i
  exact isClosed_Icc.measurableSet.preimage (by unfold constrainedAtTotal; fun_prop)

/-- The actual current produced when the genuine physical transport is
multiplied by the smooth equality-puncture cutoff. -/
def preferredRightPunctureFlux {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (ε R : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∑ i,(preferredEqualityCutoffPartial R θ i:ℂ)*
    preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i*
    preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) θ

theorem preferredRightPunctureFlux_zero_outside {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (rcut : ℝ → ℝ) (j : ℕ) (ε : ℝ)
    {R : ℝ} (hR : 0<R) (θ : Fin N → ℝ) (hdiam : R<preferredAngularDiameter θ) :
    preferredRightPunctureFlux d B τ rcut j ε R θ=0 := by
  unfold preferredRightPunctureFlux
  apply Finset.sum_eq_zero
  intro i _
  rw [preferredEqualityCutoffPartial_zero_of_diameter_lt hR θ i hdiam,
    Complex.ofReal_zero,zero_mul,zero_mul]

/-- Exact cancellation of the diameter in grad(cutoff) times the physical
field. The complete scalar normalization remains inside the literal Pj. -/
theorem preferredRightPunctureFlux_pointwise (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ A : ℝ,0<A ∧ ∀ N : ℕ,∀ τ ε R C : ℝ,0<R → 0<C →
      ∀ rcut : ℝ → ℝ,∀ j : ℕ,∀ θ : Fin N → ℝ,
      (0<preferredAngularDiameter θ → ∀ i,
        ‖preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖≤
          C*(N:ℝ)^2/preferredAngularDiameter θ) →
      ‖preferredRightPunctureFlux d B τ rcut j ε R θ‖≤A*C*(N:ℝ)^5/R^2*
        ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖ := by
  obtain ⟨A,hA,hpartial⟩ := preferredEqualityCutoffPartial_bound
  refine ⟨A,hA,?_⟩
  intro N τ ε R C hR hC rcut j θ hfield
  let P := preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
    (IsingBulk.Branch.radialParameter d.alpha ε) θ
  have hterm (i : Fin N) :
      ‖(preferredEqualityCutoffPartial R θ i:ℂ)*
        preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i*P‖≤
      A*C*(N:ℝ)^4/R^2*‖P‖ := by
    by_cases hd : 0<preferredAngularDiameter θ
    · rw [norm_mul,norm_mul,Complex.norm_real]
      have hh := mul_le_mul (hpartial N R hR θ i) (hfield hd i) (norm_nonneg _) (by positivity)
      calc
        _ ≤ ((A*(N:ℝ)^2*preferredAngularDiameter θ/R^2)*(C*(N:ℝ)^2/preferredAngularDiameter θ))*‖P‖ :=
          mul_le_mul_of_nonneg_right hh (norm_nonneg _)
        _ = _ := by field_simp [hd.ne']
    · have hz : preferredAngularDiameter θ=0 := le_antisymm (le_of_not_gt hd) Metric.diam_nonneg
      have hh := hpartial N R hR θ i
      rw [hz,mul_zero,zero_div] at hh
      have hp : preferredEqualityCutoffPartial R θ i=0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
      rw [hp,Complex.ofReal_zero,zero_mul,zero_mul,norm_zero]
      positivity
  unfold preferredRightPunctureFlux
  calc
    _ ≤ ∑ i : Fin N,‖(preferredEqualityCutoffPartial R θ i:ℂ)*
        preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i*P‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin N,A*C*(N:ℝ)^4/R^2*‖P‖ := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- Physical support also holds for the puncture current; no statement
about the singular ambient field outside that support is needed. -/
theorem preferredRightPunctureFlux_lintegral_support {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (τ : ℝ) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (j : ℕ) (ε R : ℝ) :
    (∫⁻ θ : Fin n → ℝ in angularBox n,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε R
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖)=
    ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε R
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖ := by
  let f := fun θ : Fin n → ℝ => ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε R
    (preferredLiftedAngles B.delta (constrainedAngles θ))‖
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hsupp : Function.support ((angularBox n).indicator f)⊆preferredRightRegion d B δB := by
    intro θ hθ
    by_contra hn
    by_cases hb : θ∈angularBox n
    · have hz := preferredTransportedDensity_right_support d B τ rcut hcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) _
        (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
        (by intro hh; exact hn ⟨hb,hh⟩)
      have hf : f θ=0 := by simp only [f,preferredRightPunctureFlux,hz,mul_zero,Finset.sum_const_zero,norm_zero,ENNReal.ofReal_zero]
      exact hθ (by rw [Set.indicator_of_mem hb,hf])
    · exact hθ (Set.indicator_of_notMem hb _)
  apply le_antisymm
  · calc
      _ = ∫⁻ θ,(angularBox n).indicator f θ := (lintegral_indicator hbox f).symm
      _ = ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,(angularBox n).indicator f θ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)
  · exact lintegral_mono_set (fun θ hθ => hθ.1)

/-- Quantitative actual absolute puncture current. The constant precedes
both epsilon and the dyadic puncture index, so the passage is uniform on
every compact positive-epsilon interval. -/
theorem preferred_right_puncture_flux_uniform_bound_of_q28 {n k j : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k)
    (hj : j≤k) (hN : 2*k+4<n+1) (hEven : Even (n+1))
    {C : ℝ} (hC : 0<C)
    (hfield : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ θ : Fin (n+1) → ℝ,
      θ∈preferredRightAngularBox d B.delta δB (n+1) → 0<preferredAngularDiameter θ → ∀ i,
      ‖preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i‖≤
        C*((n+1:ℕ):ℝ)^2/preferredAngularDiameter θ) :
    ∃ L : ℝ,0<L ∧ ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
    (∫⁻ θ : Fin n → ℝ in angularBox n,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε (preferredDyadicRadius m)
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal (L*(1+|Real.log ε|)*(1/2:ℝ)^m) := by
  obtain ⟨A,hA,hpoint⟩ := preferredRightPunctureFlux_pointwise d B
  obtain ⟨D,J,hD,hsmall⟩ := preferred_right_small_mass_of_q28 d B hcut.2.1
    preferredPopulationCutoff rcut k hq28 j hj
  let F := 6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope D J (n+1)
  let L := A*C*((n+1:ℕ):ℝ)^5*F/Real.pi^2
  have hL : 0<L := by dsimp [L,F,shellOrderEnvelope]; positivity
  refine ⟨L,hL,?_⟩
  intro ε hε hεr m
  let H := 1+|Real.log ε|
  let K := F*H
  have hK : 0≤K := by dsimp [K,F,H,shellOrderEnvelope]; positivity
  let R := preferredDyadicRadius m
  let Q := A*C*((n+1:ℕ):ℝ)^5/R^2
  have hR : 0<R := preferredDyadicRadius_pos m
  have hQ : 0≤Q := by dsimp [Q]; positivity
  rw [preferredRightPunctureFlux_lintegral_support d B τ rcut hcut j ε R]
  have hdom : (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε R
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal Q*(∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ) := by
    calc
      _ ≤ ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
          ENNReal.ofReal Q*preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ := by
        apply setLIntegral_mono' (preferredRightRegion_measurable d B hcut.2.1)
        intro θ hθ
        let w := preferredLiftedAngles B.delta (constrainedAngles θ)
        by_cases hd : preferredAngularDiameter w≤R
        · have hh := hpoint (n+1) τ ε R C hR hC rcut j w (hfield ε hε hεr w hθ.2)
          unfold preferredRightSmallMassIntegrand
          rw [ite_eq_left hd,←ENNReal.ofReal_mul hQ]
          exact ENNReal.ofReal_le_ofReal hh
        · have hz := preferredRightPunctureFlux_zero_outside d B τ rcut j ε hR w (lt_of_not_ge hd)
          rw [hz,norm_zero,ENNReal.ofReal_zero]
          exact bot_le
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hmul : ENNReal.ofReal Q*(∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
      preferredRightSmallMassIntegrand d B τ preferredPopulationCutoff rcut j ε m θ)≤
      ENNReal.ofReal Q*ENNReal.ofReal
        (6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope D J (n+1)*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
    simpa only [mul_comm] using mul_le_mul_left (hsmall n hN hEven ε hε hεr m) (ENNReal.ofReal Q)
  have hh := hdom.trans hmul
  rw [←ENNReal.ofReal_mul hQ] at hh
  apply hh.trans_eq
  congr 1
  have hR2 : R^2=Real.pi^2*(1/4:ℝ)^m := by
    have hRad : R=Real.pi*(1/2:ℝ)^m := by
      dsimp [R,preferredDyadicRadius]
      rw [pow_succ]
      ring
    rw [hRad,mul_pow,←pow_mul,show m*2=2*m by omega,pow_mul]
    norm_num
  change (A*C*((n+1:ℕ):ℝ)^5/R^2)*(K*(1/8:ℝ)^m)=L*H*(1/2:ℝ)^m
  rw [hR2]
  calc
    _ = (L*H)*((1/8:ℝ)^m/(1/4:ℝ)^m) := by dsimp [L,K]; ring
    _ = _ := by rw [←div_pow]; norm_num


/-- The quantitative current bound gives genuine vanishing of the actual
absolute flux along the smooth equality-puncture exhaustion. -/
theorem preferred_right_puncture_flux_tendsto_of_q28 {n k j : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ ε : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k)
    (hj : j≤k) (hN : 2*k+4<n+1) (hEven : Even (n+1)) (hε : 0<ε) (hεr : ε<ε₀)
    {C : ℝ} (hC : 0<C)
    (hfield : ∀ e : ℝ,0<e → e<ε₀ → ∀ θ : Fin (n+1) → ℝ,
      θ∈preferredRightAngularBox d B.delta δB (n+1) → 0<preferredAngularDiameter θ → ∀ i,
      ‖preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha e) θ i‖≤
        C*((n+1:ℕ):ℝ)^2/preferredAngularDiameter θ) :
    Tendsto (fun m : ℕ => ∫⁻ θ : Fin n → ℝ in angularBox n,
      ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε (preferredDyadicRadius m)
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖) atTop (𝓝 0) := by
  obtain ⟨L,_hL,hbound⟩ := preferred_right_puncture_flux_uniform_bound_of_q28 d B rcut hcut hq28 hj hN hEven hC hfield
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (L*(1+|Real.log ε|)*(1/2:ℝ)^m)) atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).const_mul (L*(1+|Real.log ε|))
    simpa only [mul_zero,ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (hbound ε hε hεr)


/-- All source-field premises in the puncture theorem are discharged on the
actual whole right contour. The remaining q28 premise is precisely the
scalar-word quantitative cut, and is not an assumed global transport rule. -/
theorem preferred_actual_right_puncture_flux (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ ε₀ τ₀ δ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut → ∀ k : ℕ,
      PreferredAllDiameterShellBound d B δB τ ε₁ preferredPopulationCutoff rcut k →
      ∀ j : ℕ,j≤k → ∀ n : ℕ,2*k+4<n+1 → Even (n+1) →
      ∀ ε : ℝ,0<ε → ε<ε₁ →
      Tendsto (fun m : ℕ => ∫⁻ θ : Fin n → ℝ in angularBox n,
        ENNReal.ofReal ‖preferredRightPunctureFlux d B τ rcut j ε (preferredDyadicRadius m)
          (preferredLiftedAngles B.delta (constrainedAngles θ))‖) atTop (𝓝 0) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := preferred_actual_angular_field_bound d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨C,ε₀,τ₀,δ₀,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hfield⟩ := hsource B hBcap
  refine ⟨ε₀,τ₀,δ₀,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro δB τ ε₁ _hδB hδB₀ hτ hτr hε₁₀ rcut hcut k hq j hj n hN hEven ε hε hεr
  apply preferred_right_puncture_flux_tendsto_of_q28 d B rcut hcut hq hj hN hEven hε hεr hC
  intro e he her θ hθ hd i
  apply hfield (n+1) (by omega) e τ he (her.trans_le hε₁₀) hτ hτr θ _ hd i
  intro a
  exact ⟨by linarith [(hθ a).1],(hθ a).2⟩

end
end IsingBulk.Preferred22
