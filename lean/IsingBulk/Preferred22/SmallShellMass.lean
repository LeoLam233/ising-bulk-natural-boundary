import IsingBulk.Preferred22.ShellAggregation
import IsingBulk.Preferred22.ShellScaleBound
import IsingBulk.Preferred22.RightShellMeasure

/-! Actual small-equality-tube mass from the complete constrained shells.
The even particle cutoff leaves enough decay for a genuine puncture flux,
not only integrability of the density. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

theorem preferredDyadicRadius_strictAnti : StrictAnti preferredDyadicRadius := by
  apply strictAnti_nat_of_succ_lt
  intro m
  unfold preferredDyadicRadius
  rw [pow_succ]
  nlinarith [mul_pos Real.pi_pos (pow_pos (by norm_num : (0:ℝ)<1/2) (m+1))]

theorem large_even_order_shell_exponent_four {N j k : ℕ}
    (hj : j≤k) (hN : 2*k+4<N) (hEven : Even N) : 4≤shellExponent N j := by
  obtain ⟨v,hv⟩ := hEven
  have hN' : 2*k+6≤N := by omega
  have hn : 2*(k:ℝ)+6≤N := by exact_mod_cast hN'
  have hj' : (j:ℝ)≤k := by exact_mod_cast hj
  unfold shellExponent
  linarith

theorem preferredDyadicRadius_power_four_bound (N j m : ℕ)
    (hq : 4≤shellExponent N j) :
    (preferredDyadicRadius m)^(shellExponent N j)≤(2*Real.pi)^N*(1/16:ℝ)^m := by
  have hqN : shellExponent N j≤(N:ℝ) := by
    unfold shellExponent
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    linarith
  have hRq := Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi] : 1≤2*Real.pi) hqN
  rw [Real.rpow_natCast] at hRq
  have hb : (0:ℝ)<(1/2:ℝ)^(m+1) := by positivity
  have hb1 : (1/2:ℝ)^(m+1)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hd := Real.rpow_le_rpow_of_exponent_ge hb hb1 hq
  have hfour : ((1/2:ℝ)^(m+1))^(4:ℝ)=(1/16:ℝ)^(m+1) := by
    rw [Real.rpow_ofNat,←pow_mul,show (m+1)*4=4*(m+1) by omega,pow_mul]
    norm_num
  rw [hfour] at hd
  have hm : (1/16:ℝ)^(m+1)≤(1/16:ℝ)^m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold preferredDyadicRadius
  rw [Real.mul_rpow (by positivity : 0≤2*Real.pi) hb.le]
  exact mul_le_mul hRq (hd.trans hm) (by positivity) (by positivity)

/-- Actual absolute mass inside a shrinking equality tube. The function is
kept in the original free angles and the exact one-sided lift. -/
def preferredRightSmallMassIntegrand {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (τ : ℝ) (η rcut : ℝ → ℝ) (j : ℕ) (ε : ℝ) (m : ℕ) (θ : Fin n → ℝ) : ℝ≥0∞ :=
  if preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles θ))≤preferredDyadicRadius m then
    ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖
  else 0

/-- q28 gives a cubic dyadic small-tube decay for every allowed even large
order. This leaves a positive power after the two puncture-flux losses. -/
theorem preferred_right_small_mass_of_q28 (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (hδB : δB<B.delta) (η rcut : ℝ → ℝ) (k : ℕ)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ η rcut k) :
    ∀ j : ℕ,j≤k → ∃ C : ℝ,∃ J : ℕ,0<C ∧ ∀ n : ℕ,2*k+4<n+1 → Even (n+1) →
      ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightSmallMassIntegrand d B τ η rcut j ε m θ)≤
      ENNReal.ofReal (6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope C J (n+1)*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
  intro j hj
  obtain ⟨C,J,hC,hshell⟩ := hq28 j hj
  refine ⟨2*Real.pi*C,J,by positivity,?_⟩
  intro n hN hEven ε hε hεr m
  let N := n+1
  let H := 1+|Real.log ε|
  let K := shellOrderEnvelope (2*Real.pi*C) J N*H
  have hN2 : 2≤N := by dsimp [N]; omega
  have hN0 : 0<N := by omega
  have hH : 0≤H := by dsimp [H]; positivity
  have hK : 0≤K := by dsimp [K,shellOrderEnvelope]; positivity
  have hq := large_even_order_shell_exponent_four hj hN hEven
  have hb := preferredRightRegion_lintegral_geometric (by omega : 0<n) d B hδB
    (preferredRightSmallMassIntegrand d B τ η rcut j ε m)
    (mul_nonneg hK (by positivity : 0≤(1/8:ℝ)^m)) ?_
  · simpa only [K,N,H,mul_assoc] using hb
  intro l z i a
  by_cases hlm : m≤l
  · have hdom : (∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius l) z.1 i a,
        preferredRightSmallMassIntegrand d B τ η rcut j ε m θ)≤
        ∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius l) z.1 i a,
          ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
            (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖ := by
      apply lintegral_mono
      intro θ
      unfold preferredRightSmallMassIntegrand
      split_ifs <;> simp
    obtain ⟨hi,hmass⟩ := hshell n hN2 hEven ε (preferredDyadicRadius l) hε hεr
      (preferredDyadicRadius_pos l) z.1 i a
    have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    change ENNReal.ofReal (preferredRightShellMass d B δB τ η rcut j ε (preferredDyadicRadius l) z.1 i a)=_ at he
    rw [←he] at hdom
    apply hdom.trans
    apply ENNReal.ofReal_le_ofReal
    have hr := preferredDyadicRadius_pos l
    have hcompare := every_diameter_shell_comparison hr
      (preferredShellScale_ge_diameter d N z.1 (preferredDyadicRadius l) hε.le) hN2 j
    have hpower := preferredDyadicRadius_power_four_bound N j l hq
    have henv : 0≤shellOrderEnvelope C J N := by unfold shellOrderEnvelope; positivity
    have hpow : shellOrderEnvelope C J N*(2*Real.pi)^N=shellOrderEnvelope (2*Real.pi*C) J N := by
      unfold shellOrderEnvelope
      rw [mul_div_assoc,mul_pow]
      ring
    have hshift : (1/16:ℝ)^l≤(1/8:ℝ)^m*(1/2:ℝ)^l := by
      calc
        _ = (1/8:ℝ)^l*(1/2:ℝ)^l := by rw [←mul_pow]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hlm) (by positivity)
    rw [←shell_order_envelope_eq_rpow C J N hN0] at hmass
    calc
      _ ≤ shellOrderEnvelope C J N*((preferredDyadicRadius l)^(shellExponent N j))*H := by
        exact hmass.trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcompare henv) hH)
      _ ≤ shellOrderEnvelope C J N*((2*Real.pi)^N*(1/16:ℝ)^l)*H :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower henv) hH
      _ = K*(1/16:ℝ)^l := by rw [←mul_assoc,hpow]; dsimp [K]; ring
      _ ≤ K*(1/8:ℝ)^m*(1/2:ℝ)^l := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hshift hK
  · have hlm' : l<m := Nat.lt_of_not_ge hlm
    have hzero (θ : Fin n → ℝ) (hθ : θ∈preferredRightShell d B δB (preferredDyadicRadius l) z.1 i a) :
        preferredRightSmallMassIntegrand d B τ η rcut j ε m θ=0 := by
      unfold preferredRightSmallMassIntegrand
      apply ite_eq_right
      have hd := preferredRightShell_diameter_lower d B (preferredDyadicRadius_pos l) hθ
      exact not_le.mpr ((preferredDyadicRadius_strictAnti hlm').trans_le hd)
    have hmeas : MeasurableSet (preferredRightShell d B δB (preferredDyadicRadius l) z.1 i a) := by
      rw [preferredRightShell_eq_linear d B hδB]
      exact (preferredLinearRightShell_isClosed d B δB (preferredDyadicRadius l) z.1 i a).measurableSet
    rw [setLIntegral_congr_fun hmeas hzero,lintegral_zero]
    exact bot_le

end
end IsingBulk.Preferred22
