import IsingBulk.Preferred22.ShellCover
import IsingBulk.Preferred22.ZerothShellTheorem

/-! Genuine summation of the actual constrained mean/extrema/dyadic shell
integrals. Positive transport orders retain the exact q28 premise, while
the order-zero physical instance is supplied by the proved source theorem. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

/-- All fixed radii have one geometric majorant uniform in the large
particle order and every allowed derivative index. -/
theorem preferredDyadicRadius_power_bound (N j m : ℕ)
    (hq : 1≤shellExponent N j) :
    (preferredDyadicRadius m)^(shellExponent N j)≤(2*Real.pi)^N*(1/2:ℝ)^m := by
  have hR : 1≤2*Real.pi := by linarith [Real.two_le_pi]
  have hqN : shellExponent N j≤(N:ℝ) := by
    unfold shellExponent
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    linarith
  have hRq := Real.rpow_le_rpow_of_exponent_le hR hqN
  rw [Real.rpow_natCast] at hRq
  have hd := dyadic_shell_le_geometric hq (m+1)
  have hdm : (1/2:ℝ)^(m+1)≤(1/2:ℝ)^m := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) m]
  unfold preferredDyadicRadius
  rw [Real.mul_rpow (by positivity : 0≤2*Real.pi) (by positivity : 0≤(1/2:ℝ)^(m+1))]
  exact mul_le_mul hRq (hd.trans hdm) (by positivity) (by positivity)

/-- Finite means and named extrema are actually counted inside the
nonnegative integral; the final dyadic sum is the complete infinite sum. -/
theorem preferredRightRegion_lintegral_geometric {n : ℕ} (hn : 0<n)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (f : (Fin n → ℝ) → ℝ≥0∞) {K : ℝ} (hK : 0≤K)
    (hb : ∀ m : ℕ,∀ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∀ i a : Fin (n+1),
      (∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a,f θ)≤
        ENNReal.ofReal (K*(1/2:ℝ)^m)) :
    (∫⁻ θ in preferredRightRegion d B δB,f θ)≤ENNReal.ofReal (6*((n+1:ℕ):ℝ)^3*K) := by
  let L := ((preferredMeanIndices (n+1)).card:ℝ)*((n+1:ℕ):ℝ)*((n+1:ℕ):ℝ)
  have hL : 0≤L := by dsimp [L]; positivity
  have hterm (m : ℕ) :
      (∑ l : {l : ℤ // l∈preferredMeanIndices (n+1)},∑ i : Fin (n+1),∑ a : Fin (n+1),
        ∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius m) l.1 i a,f θ)≤
      ENNReal.ofReal (L*K*(1/2:ℝ)^m) := by
    calc
      _ ≤ ∑ _l : {l : ℤ // l∈preferredMeanIndices (n+1)},∑ _i : Fin (n+1),∑ _a : Fin (n+1),
          ENNReal.ofReal (K*(1/2:ℝ)^m) := by
        apply Finset.sum_le_sum
        intro l _
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum (fun a _ => hb m l i a)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul]
        have hLc : ENNReal.ofReal L=((preferredMeanIndices (n+1)).card:ℝ≥0∞)*((n+1:ℕ):ℝ≥0∞)*((n+1:ℕ):ℝ≥0∞) := by
          dsimp [L]
          rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
          simp only [ENNReal.ofReal_natCast]
        rw [show L*K*(1/2:ℝ)^m=L*(K*(1/2:ℝ)^m) by ring,ENNReal.ofReal_mul hL,hLc]
        ring
  have hsum : Summable (fun m : ℕ => L*K*(1/2:ℝ)^m) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left (L*K)
  have hgeo : (∑' m : ℕ,(1/2:ℝ)^m)=2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]
    norm_num
  have hcount : ((preferredMeanIndices (n+1)).card:ℝ)≤3*((n+1:ℕ):ℝ) := by
    exact_mod_cast preferredMeanIndices_card_le (by omega : 0<n+1)
  calc
    _ ≤ ∑' m : ℕ,ENNReal.ofReal (L*K*(1/2:ℝ)^m) :=
      (preferredRightRegion_lintegral_le_shells hn d B hδB f).trans (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (L*K*2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum,tsum_mul_left,hgeo]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_right hcount (by positivity : 0≤((n+1:ℕ):ℝ)^2*K)])

/-- The full source region inherits an explicit particle envelope from the
literal q28 statement. This theorem does not replace that statement by an
assumed complete tail. -/
theorem preferred_right_region_bound_of_q28 (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ ε₀ : ℝ} (hδB : δB<B.delta) (η rcut : ℝ → ℝ) (k : ℕ)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ η rcut k) :
    ∀ j : ℕ,j≤k → ∃ C : ℝ,∃ J : ℕ,0<C ∧ ∀ n : ℕ,2*k+4<n+1 → Even (n+1) →
      ∀ ε : ℝ,0<ε → ε<ε₀ →
      (∫⁻ (θ : Fin n → ℝ) in preferredRightRegion d B δB,ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal (6*((n+1:ℕ):ℝ)^3*shellOrderEnvelope C J (n+1)*(1+|Real.log ε|)) := by
  intro j hj
  obtain ⟨C,J,hC,hshell⟩ := hq28 j hj
  refine ⟨2*Real.pi*C,J,by positivity,?_⟩
  intro n hN hEven ε hε hεr
  let N := n+1
  let H := 1+|Real.log ε|
  let K := shellOrderEnvelope (2*Real.pi*C) J N*H
  have hN2 : 2≤N := by dsimp [N]; omega
  have hN0 : 0<N := by omega
  have hH : 0≤H := by dsimp [H]; positivity
  have hK : 0≤K := by dsimp [K,shellOrderEnvelope]; positivity
  have hq := large_order_shell_exponent hj hN
  have hb := preferredRightRegion_lintegral_geometric (by omega : 0<n) d B hδB
    (fun θ => ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖)
    hK ?_
  · simpa only [K,N,H,mul_assoc] using hb
  intro m l i a
  obtain ⟨hi,hmass⟩ := hshell n hN2 hEven ε (preferredDyadicRadius m) hε hεr
    (preferredDyadicRadius_pos m) l.1 i a
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  change ENNReal.ofReal (preferredRightShellMass d B δB τ η rcut j ε (preferredDyadicRadius m) l.1 i a)=_ at he
  rw [← he]
  apply ENNReal.ofReal_le_ofReal
  have hr := preferredDyadicRadius_pos m
  have hc := every_diameter_shell_comparison hr
    (preferredShellScale_ge_diameter d N l.1 (preferredDyadicRadius m) hε.le) hN2 j
  have hd := preferredDyadicRadius_power_bound N j m hq
  have henv : 0≤shellOrderEnvelope C J N := by unfold shellOrderEnvelope; positivity
  have hpow : shellOrderEnvelope C J N*(2*Real.pi)^N=shellOrderEnvelope (2*Real.pi*C) J N := by
    unfold shellOrderEnvelope
    rw [mul_div_assoc,mul_pow]
    ring
  rw [← shell_order_envelope_eq_rpow C J N hN0] at hmass
  calc
    _ ≤ shellOrderEnvelope C J N*
        ((preferredDyadicRadius m)^(2*(N:ℝ)-2*(j:ℝ)-3)*
          (preferredShellScale d N l.1 (preferredDyadicRadius m) ε)^(-(N:ℝ)+3/2))*H := by
      simpa only [N,H,mul_assoc] using hmass
    _ ≤ shellOrderEnvelope C J N*(preferredDyadicRadius m)^(shellExponent N j)*H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc henv) hH
    _ ≤ shellOrderEnvelope C J N*((2*Real.pi)^N*(1/2:ℝ)^m)*H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd henv) hH
    _ = K*(1/2:ℝ)^m := by rw [← mul_assoc, hpow]; dsimp [K]; ring

end
end IsingBulk.Preferred22
