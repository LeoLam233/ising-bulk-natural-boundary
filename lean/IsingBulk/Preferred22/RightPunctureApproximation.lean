import IsingBulk.Preferred22.ActualShellTheorem
import IsingBulk.Preferred22.PunctureFlux
import IsingBulk.Preferred22.RightMassTail
import IsingBulk.Preferred22.PhysicalDensityShell

/-! Actual complex Bochner integrability and quantitative approximation by
smooth equality punctures. These estimates use the genuine constrained shell
cover and the original angular lift; its seam is never treated as continuous. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff

/-- Any multiplier of the actual transported right density has the same
true right support, without a measurability assumption on the multiplier. -/
theorem preferred_weighted_right_lintegral_support {n : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB : ℝ} (τ : ℝ) (rcut : ℝ → ℝ)
    (hcut : PreferredRightCutoffData d B δB rcut) (j : ℕ) (s : ℂ)
    (w : (Fin (n+1) → ℝ) → ℂ) :
    (∫⁻ θ : Fin n → ℝ in angularBox n,ENNReal.ofReal
      ‖w (preferredLiftedAngles B.delta (constrainedAngles θ))*
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
          (preferredLiftedAngles B.delta (constrainedAngles θ))‖)=
    ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,ENNReal.ofReal
      ‖w (preferredLiftedAngles B.delta (constrainedAngles θ))*
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
          (preferredLiftedAngles B.delta (constrainedAngles θ))‖ := by
  let f := fun θ : Fin n → ℝ => ENNReal.ofReal
    ‖w (preferredLiftedAngles B.delta (constrainedAngles θ))*
      preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hsupp : Function.support ((angularBox n).indicator f)⊆preferredRightRegion d B δB := by
    intro θ hθ
    by_contra hn
    by_cases hb : θ∈angularBox n
    · have hz := preferredTransportedDensity_right_support d B τ rcut hcut j s _
        (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
        (by intro hh; exact hn ⟨hb,hh⟩)
      exact hθ (by simp only [Set.indicator_of_mem hb,f,hz,mul_zero,norm_zero,ENNReal.ofReal_zero])
    · exact hθ (Set.indicator_of_notMem hb _)
  apply le_antisymm
  · calc
      _ = ∫⁻ θ,(angularBox n).indicator f θ := (lintegral_indicator hbox f).symm
      _ = ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,(angularBox n).indicator f θ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)
  · exact lintegral_mono_set (fun θ hθ => hθ.1)

/-- Actual complex shell integrability, together with its proved norm mass,
gives genuine full-Haar integrability for every continuous bounded weight. -/
theorem preferred_right_weighted_integrable_of_shells {n : ℕ} (hn : 0<n)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (τ : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ)
    (hcomplex : ∀ m : ℕ,∀ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∀ i a : Fin (n+1),
      IntegrableOn (fun θ : Fin n → ℝ =>
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
          (preferredLiftedAngles B.delta (constrainedAngles θ)))
        (preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a))
    (hnorm : IntegrableOn (fun θ : Fin n → ℝ =>
      ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖) (angularBox n))
    (w : (Fin (n+1) → ℝ) → ℂ) (hw : Continuous w) (hwb : ∀ θ,‖w θ‖≤1) :
    IntegrableOn (fun θ : Fin n → ℝ => w (preferredLiftedAngles B.delta (constrainedAngles θ))*
      preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAngles θ))) (angularBox n) := by
  let P := fun θ : Fin n → ℝ => preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
    (preferredLiftedAngles B.delta (constrainedAngles θ))
  let W := fun θ : Fin n → ℝ => w (preferredLiftedAngles B.delta (constrainedAngles θ))*P θ
  have hle (θ : Fin n → ℝ) : ‖W θ‖≤‖P θ‖ := by
    dsimp [W]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hwb _) (norm_nonneg _)).trans_eq (one_mul _)
  have hnormr : IntegrableOn (fun θ => ‖P θ‖) (preferredRightRegion d B δB) :=
    hnorm.mono_set (fun _ h => h.1)
  have hf : (∫⁻ θ in preferredRightRegion d B δB,ENNReal.ofReal ‖P θ‖)<(∞:ℝ≥0∞) := by
    simpa only [norm_norm] using (hasFiniteIntegral_iff_norm (fun θ => ‖P θ‖)).mp hnormr.2
  have hi : IntegrableOn W (preferredRightRegion d B δB) := by
    apply preferredRightRegion_integrable_of_shells hn d B hcut.2.1 W
    · intro m l i a
      have hm : MeasurableSet (preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a) := by
        rw [preferredRightShell_eq_linear d B hcut.2.1]
        exact (preferredLinearRightShell_isClosed d B δB (preferredDyadicRadius m) l.1 i a).measurableSet
      have hwc : ContinuousOn (fun θ : Fin n → ℝ => w (preferredLiftedAngles B.delta (constrainedAngles θ)))
          (preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a) := by
        rw [preferredRightShell_eq_linear d B hcut.2.1]
        have hc : Continuous (fun θ : Fin n → ℝ => w (constrainedAtTotal (2*Real.pi*(l.1:ℝ)) θ)) :=
          hw.comp (by unfold constrainedAtTotal; fun_prop)
        apply hc.continuousOn.congr
        intro θ hθ
        dsimp only
        rw [(preferred_lift_eq_affine_from_right d B hcut.2.1 l.1 θ hθ.1).2]
      exact (hcomplex m l i a).bdd_mul (hwc.aestronglyMeasurable hm)
        (Filter.Eventually.of_forall (fun θ => hwb _))
    · exact (lintegral_mono (fun θ => ENNReal.ofReal_le_ofReal (hle θ))).trans_lt hf
  apply hi.of_forall_sdiff_eq_zero (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
  intro θ hθ
  have hz := preferredTransportedDensity_right_support d B τ rcut hcut j s _
    (preferredLiftedAngles_mem_oneSided B.delta (constrainedAngles θ))
    (by intro hh; exact hθ.2 ⟨hθ.1,hh⟩)
  simp only [W,P,hz,mul_zero]

/-- The exact smooth puncture has a uniform 8^-m approximation error on
full Haar integrals. Integrability is genuine complex Bochner integrability. -/
theorem preferred_right_puncture_error_of_q28 {n k j : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k)
    (hj : j≤k) (hN : 2*k+4<n+1) (hEven : Even (n+1))
    (hcomplex : ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      ∀ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∀ i a : Fin (n+1),
      IntegrableOn (fun θ : Fin n → ℝ =>
        preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ)))
        (preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a)) :
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
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|)*(1/8:ℝ)^m := by
  obtain ⟨C,J,hC,hsmall⟩ := preferred_right_small_mass_of_q28 d B hcut.2.1
    preferredPopulationCutoff rcut k hq28 j hj
  obtain ⟨_D,_K,_hD,hmass⟩ := preferred_right_absolute_bound_of_q28 d B rcut hcut k hq28 j hj
  let A := 6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope C J (n+1)
  have hA : 0<A := by dsimp [A,shellOrderEnvelope]; positivity
  refine ⟨A,hA,?_⟩
  intro ε hε hεr
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let P := fun θ : Fin n → ℝ => preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j s
    (preferredLiftedAngles B.delta (constrainedAngles θ))
  have hn := (hmass n hN hEven ε hε hεr).1
  have hi : IntegrableOn P (angularBox n) := by
    have hh := preferred_right_weighted_integrable_of_shells (by omega : 0<n) d B τ rcut hcut j s
      (hcomplex ε hε hεr) hn (fun _ => 1) continuous_const (by intro θ; simp)
    simpa only [one_mul] using hh
  refine ⟨hi,?_⟩
  intro m
  let R := preferredDyadicRadius m
  let ξ := fun θ : Fin (n+1) → ℝ => (preferredEqualityCutoff R θ:ℂ)
  have hξc : Continuous ξ := Complex.continuous_ofReal.comp (preferredEqualityCutoff_smooth R).continuous
  have hξb (θ : Fin (n+1) → ℝ) : ‖ξ θ‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (preferredEqualityCutoff_bounds R θ).1]
    exact (preferredEqualityCutoff_bounds R θ).2
  have hξi := preferred_right_weighted_integrable_of_shells (by omega : 0<n) d B τ rcut hcut j s
    (hcomplex ε hε hεr) hn ξ hξc hξb
  refine ⟨hξi,?_⟩
  let W := fun θ : Fin n → ℝ => (ξ (preferredLiftedAngles B.delta (constrainedAngles θ))-1)*P θ
  have he : (fun θ : Fin n → ℝ => ξ (preferredLiftedAngles B.delta (constrainedAngles θ))*P θ-P θ)=W := by
    funext θ
    dsimp [W]
    ring
  change ‖(∫ θ in angularBox n,ξ (preferredLiftedAngles B.delta (constrainedAngles θ))*P θ)-
    ∫ θ in angularBox n,P θ‖≤_
  rw [←integral_sub hξi hi,he]
  have hsupp : (∫⁻ θ : Fin n → ℝ in angularBox n,ENNReal.ofReal ‖W θ‖)=
      ∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,ENNReal.ofReal ‖W θ‖ :=
    preferred_weighted_right_lintegral_support d B τ rcut hcut j s (fun θ => ξ θ-1)
  have hdom : (∫⁻ θ : Fin n → ℝ in angularBox n,ENNReal.ofReal ‖W θ‖)≤
      ENNReal.ofReal (A*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
    rw [hsupp]
    apply le_trans (lintegral_mono (fun θ => ?_)) (hsmall n hN hEven ε hε hεr m)
    let w := preferredLiftedAngles B.delta (constrainedAngles θ)
    by_cases hd : preferredAngularDiameter w≤R
    · unfold preferredRightSmallMassIntegrand
      rw [ite_eq_left hd]
      apply ENNReal.ofReal_le_ofReal
      change ‖(ξ w-1)*P θ‖≤‖P θ‖
      rw [norm_mul]
      have hb : ‖ξ w-1‖≤1 := by
        have hh := preferredEqualityCutoff_bounds R w
        rw [show ξ w-1=((preferredEqualityCutoff R w-1:ℝ):ℂ) by simp only [ξ,Complex.ofReal_sub,Complex.ofReal_one],
          Complex.norm_real,Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)
    · have hx := preferredEqualityCutoff_one_of_diameter_lt (preferredDyadicRadius_pos m) w (lt_of_not_ge hd)
      have hz : W θ=0 := by
        change ((preferredEqualityCutoff (preferredDyadicRadius m) w:ℂ)-1)*P θ=0
        rw [hx,Complex.ofReal_one,sub_self,zero_mul]
      rw [hz,norm_zero,ENNReal.ofReal_zero]
      exact bot_le
  have hnA : 0≤A*(1+|Real.log ε|)*(1/8:ℝ)^m := by positivity
  exact (norm_integral_le_lintegral_norm W).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hdom).trans_eq (ENNReal.toReal_ofReal hnA))

/-- Unconditional actual large-order complex integrability and puncture
approximation on one regime, with no shell, norm or regularity premise. -/
theorem preferred_actual_right_puncture_approximation (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB : ℝ,0<δB → δB≤δ₀ → ∀ rcut : ℝ → ℝ,
      PreferredRightCutoffData d B δB rcut → ∀ τ : ℝ,0≤τ → τ<τ₀ →
      ∀ k j n : ℕ,j≤k → 2*k+4<n+1 → Even (n+1) →
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
          (IsingBulk.Branch.radialParameter d.alpha ε)‖≤A*(1+|Real.log ε|)*(1/8:ℝ)^m := by
  obtain ⟨cs,hcs,hcsa,hs⟩ := preferred_actual_all_diameter_shell_bound d
  obtain ⟨cg,hcg,_hcga,hg⟩ := preferred_actual_all_order_shell_integrable d
  refine ⟨min cs cg,lt_min hcs hcg,(min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  obtain ⟨δs,τs,εs,hδs,hδsδ,hτs,hεs,hq⟩ := hs B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δg,τg,εg,hδg,_hδgδ,hτg,hεg,hcomplex⟩ := hg B (hBcap.trans_le (min_le_right _ _))
  let δ₀ := min δs δg
  let τ₀ := min τs τg
  let ε₀ := min εs εg
  refine ⟨δ₀,τ₀,ε₀,lt_min hδs hδg,(min_le_left _ _).trans_lt hδsδ,
    lt_min hτs hτg,lt_min hεs hεg,?_⟩
  intro δB hδB hδB₀ rcut hcut τ hτ hτr k j n hj hN hEven
  have hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ preferredPopulationCutoff rcut k :=
    (hq δB hδB (hδB₀.trans (min_le_left _ _)) rcut hcut.2.2.1 hcut.2.2.2.1 τ hτ
      (hτr.trans_le (min_le_left _ _)) k).mono_epsilon (min_le_left _ _)
  apply preferred_right_puncture_error_of_q28 d B rcut hcut hq28 hj hN hEven
  intro ε hε hεr m l i a
  have hi := hcomplex n (by omega) ε τ hε (hεr.trans_le (min_le_right _ _))
    hτ (hτr.trans_le (min_le_right _ _)) preferredPopulationCutoff rcut
    preferredPopulationCutoff_smooth hcut.2.2.1 j (preferredDyadicRadius m)
    (preferredDyadicRadius_pos m) l.1 i a
  apply hi.mono_set
  intro θ hθ
  refine ⟨hθ.1,?_,hθ.2.2⟩
  intro v
  have hm : δB≤δg := hδB₀.trans (min_le_right _ _)
  exact ⟨by linarith [(hθ.2.1 v).1],(hθ.2.1 v).2⟩

end
end IsingBulk.Preferred22
