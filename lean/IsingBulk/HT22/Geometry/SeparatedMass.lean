import IsingBulk.HT22.Geometry.SignedShellAggregation
import IsingBulk.HT22.Geometry.SignedShellUpperScale

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators ENNReal

theorem fullRightShell_diameter_le {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB r : ℝ} {i j : Fin N} {w : Fin N → ℝ} (hw : w∈preferredFullRightShell d B δB r i j) :
    preferredAngularDiameter w≤2*r := by
  apply le_trans (b := w j-w i) ?_ hw.2.2.2
  apply Metric.diam_le_of_forall_dist_le (sub_nonneg.mpr (hw.2.1 j).1)
  rintro _ ⟨k,rfl⟩ _ ⟨q,rfl⟩
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [(hw.2.1 k).1,(hw.2.1 k).2,(hw.2.1 q).1,(hw.2.1 q).2]

theorem dyadic_normalized_scale_le (μ : ℝ) (k : ℕ) {ε : ℝ} (hε : 0<ε) :
    preferredDyadicRadius k/Real.sqrt (|μ|+preferredDyadicRadius k+ε)≤Real.pi+1 := by
  have hr := preferredDyadicRadius_pos k
  have hrπ := preferredDyadicRadius_le_pi k
  have hT : 0 < |μ|+preferredDyadicRadius k+ε := by positivity
  have hs := Real.sq_sqrt hT.le
  have hs0 := Real.sqrt_nonneg (|μ|+preferredDyadicRadius k+ε)
  have hh : Real.sqrt (preferredDyadicRadius k)≤Real.pi+1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.pi_pos]
  apply le_trans ?_ hh
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hT)).mpr
  have ht := Real.sqrt_le_sqrt (show preferredDyadicRadius k≤|μ|+preferredDyadicRadius k+ε by linarith [abs_nonneg μ])
  have hp := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg (preferredDyadicRadius k))
  nlinarith [Real.sq_sqrt hr.le]

/-- Actual signed coarea mass of any diameter-separated source density.
No transported-density endpoint or integrability assumption is used. -/
theorem signed_separated_mass (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ ε₀ τ₀ δ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
    ∀ m : ℕ,∀ ρ K : ℝ,0<ρ → 0≤K → ∃ C : ℝ,0<C ∧
    ∀ a η ε τ δB : ℝ,|a|≤Real.pi → 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      0<δB → δB≤δ₀ → ∀ f : (Fin (m+3) → ℝ) → ℝ,
      (∀ w,(∀ i,w i∈Icc (-d.b-δB) B.delta) → f w≤K*signedJacobianResolvent η d B ε τ w) →
      (∀ w,preferredAngularDiameter w<ρ → f w=0) →
      (∫⁻ θ in signedRightRegion a d B δB,
        ENNReal.ofReal (f (preferredLiftedAngles B.delta (constrainedAtTotal a θ))))≤
        ENNReal.ofReal (C*(1+|Real.log ε|)) := by
  obtain ⟨A,C,e,t,δ,hA,hC,he,ht,hδ,hδB,hbound⟩ := signed_actual_shell_scale_lintegral d B
  refine ⟨e,t,δ,he,ht,hδ,hδB,?_⟩
  intro m ρ K hρ hK
  let Q := (K+1)*C*((m+3:ℕ):ℝ)*A^(m+1)*(Real.pi+1)^m*(2*Real.pi/ρ)
  have hQ : 0<Q := by dsimp [Q]; positivity
  refine ⟨6*((m+3:ℕ):ℝ)^3*Q,by positivity,?_⟩
  intro a η ε τ δB ha hε hεe hτ hτt hδB0 hδle f hf hz
  have hb (k : ℕ) (l : {l : ℤ // l∈preferredMeanIndices (m+3)}) (i j : Fin (m+3)) :
      (∫⁻ θ in signedRightShell a d B δB (preferredDyadicRadius k) l.1 i j,
        ENNReal.ofReal (f (preferredLiftedAngles B.delta (constrainedAtTotal a θ))))≤
      ENNReal.ofReal ((Q*(1+|Real.log ε|))*(1/2:ℝ)^k) := by
    by_cases hsmall : 2*preferredDyadicRadius k<ρ
    · have heq : (∫⁻ θ in signedRightShell a d B δB (preferredDyadicRadius k) l.1 i j,
          ENNReal.ofReal (f (preferredLiftedAngles B.delta (constrainedAtTotal a θ))))=0 := by
        apply setLIntegral_eq_zero (signedRightShell_isClosed a d B (hδle.trans_lt hδB) _ _ _ _).measurableSet
        intro θ hθ
        change ENNReal.ofReal (f (preferredLiftedAngles B.delta (constrainedAtTotal a θ)))=0
        rw [hz _ ((fullRightShell_diameter_le d B hθ.2.1).trans_lt hsmall),ENNReal.ofReal_zero]
      rw [heq]
      exact bot_le
    have hρk : ρ≤2*preferredDyadicRadius k := le_of_not_gt hsmall
    have hbase := hbound a η m ε τ (preferredDyadicRadius k) δB K hε hεe hτ hτt
      (preferredDyadicRadius_pos k) hδB0 hδle hK l i j f (fun x hx => hf _ hx.1)
    apply hbase.trans (ENNReal.ofReal_le_ofReal ?_)
    have hrk := (preferredDyadicRadius_pos k).le
    have hscale := pow_le_pow_left₀ (by positivity : 0≤preferredDyadicRadius k /
      Real.sqrt (|d.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)|+preferredDyadicRadius k+ε))
      (dyadic_normalized_scale_le (d.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)) k hε) m
    have hfactor : 1≤(2*Real.pi/ρ)*(1/2:ℝ)^k := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hρ).mpr
      dsimp [preferredDyadicRadius] at hρk
      rw [pow_succ] at hρk
      nlinarith
    have hcoeff : K*C*((m+3:ℕ):ℝ)*A^(m+1)*
        (preferredDyadicRadius k/Real.sqrt (|d.b+(a+2*Real.pi*(l:ℝ))/((m+3:ℕ):ℝ)|+preferredDyadicRadius k+ε))^m ≤
        (K+1)*C*((m+3:ℕ):ℝ)*A^(m+1)*(Real.pi+1)^m := by
      apply mul_le_mul ?_ hscale (by positivity) (by positivity)
      gcongr
      linarith
    have hh := mul_le_mul_of_nonneg_right hfactor
      (show 0≤(K+1)*C*((m+3:ℕ):ℝ)*A^(m+1)*(Real.pi+1)^m by positivity)
    have hh' := mul_le_mul_of_nonneg_right (hcoeff.trans (by simpa only [one_mul] using hh))
      (show 0≤1+|Real.log ε| by positivity)
    dsimp [Q]
    nlinarith [hh']
  have hh := signedRightRegion_lintegral_geometric (n := m+2) (by omega) a ha d B
    (hδle.trans_lt hδB) (fun θ => ENNReal.ofReal (f (preferredLiftedAngles B.delta (constrainedAtTotal a θ))))
    (by positivity : 0≤Q*(1+|Real.log ε|)) hb
  convert hh using 1
  congr 1
  ring

/-- Extend an actual separated-region estimate across its open zero tube. -/
theorem separated_pointwise_extend {N : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (η ε τ δB ρ K : ℝ) (hK : 0≤K) (f : (Fin N → ℝ) → ℝ)
    (hf : ∀ w,(∀ i,w i∈Icc (-d.b-δB) B.delta) → ρ≤preferredAngularDiameter w →
      f w≤K*signedJacobianResolvent η d B ε τ w)
    (hz : ∀ w,preferredAngularDiameter w<ρ → f w=0) :
    ∀ w,(∀ i,w i∈Icc (-d.b-δB) B.delta) → f w≤K*signedJacobianResolvent η d B ε τ w := by
  intro w hw
  by_cases hd : ρ≤preferredAngularDiameter w
  · exact hf w hw hd
  · rw [hz w (lt_of_not_ge hd)]
    unfold signedJacobianResolvent
    positivity

end
end IsingBulk.HT22.Geometry
