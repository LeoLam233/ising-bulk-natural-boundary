import IsingBulk.Preferred22.FiniteRightMass
import IsingBulk.Preferred22.SmallShellMass

/-! Quantitative small-equality-tube decay in the distinct finite block.
The full collision degree gives four powers, while only finitely many coarse
shells use the large-order envelope. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

theorem preferredDyadicRadius_power_four_general {Q : ℝ} (hQ : 4≤Q) (m : ℕ) :
    (preferredDyadicRadius m)^Q≤(2*Real.pi)^Q*(1/16:ℝ)^m := by
  have hb : (0:ℝ)<(1/2:ℝ)^(m+1) := by positivity
  have hb1 : (1/2:ℝ)^(m+1)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hd := Real.rpow_le_rpow_of_exponent_ge hb hb1 hQ
  have hfour : ((1/2:ℝ)^(m+1))^(4:ℝ)=(1/16:ℝ)^(m+1) := by
    rw [Real.rpow_ofNat,←pow_mul,show (m+1)*4=4*(m+1) by omega,pow_mul]
    norm_num
  rw [hfour] at hd
  have hm : (1/16:ℝ)^(m+1)≤(1/16:ℝ)^m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold preferredDyadicRadius
  rw [Real.mul_rpow (by positivity : 0≤2*Real.pi) hb.le]
  exact mul_le_mul_of_nonneg_left (hd.trans hm) (by positivity)

theorem preferred_dyadic_two_power_sixteen_envelope {E D q Q : ℝ}
    (hE : 0≤E) (hD : 0<D) (hQ : 4≤Q) (m₀ : ℕ) :
    ∃ L : ℝ,0<L ∧ ∀ m : ℕ,
      (m<m₀ → E*(preferredDyadicRadius m)^q≤L*(1/16:ℝ)^m) ∧
      (m₀≤m → D*(preferredDyadicRadius m)^Q≤L*(1/16:ℝ)^m) := by
  let P := ∑ m∈Finset.range m₀,E*(preferredDyadicRadius m)^q/(1/16:ℝ)^m
  have hP : 0≤P := Finset.sum_nonneg (fun m _ => by
    have hr := preferredDyadicRadius_pos m
    positivity)
  let L := 1+P+D*(2*Real.pi)^Q
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  intro m
  constructor
  · intro hm
    have hs : E*(preferredDyadicRadius m)^q/(1/16:ℝ)^m≤P :=
      Finset.single_le_sum (f := fun l => E*(preferredDyadicRadius l)^q/(1/16:ℝ)^l)
        (fun l (_ : l∈Finset.range m₀) => by
          have hr := preferredDyadicRadius_pos l
          positivity) (Finset.mem_range.mpr hm)
    have hPL : P≤L := by
      have hterm : 0≤D*(2*Real.pi)^Q := by positivity
      dsimp [L]
      linarith
    exact (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<1/16) m)).mp (hs.trans hPL)
  · intro _hm
    have hDL : D*(2*Real.pi)^Q≤L := by dsimp [L]; linarith
    calc
      _ ≤ D*((2*Real.pi)^Q*(1/16:ℝ)^m) :=
        mul_le_mul_of_nonneg_left (preferredDyadicRadius_power_four_general hQ m) hD.le
      _ ≤ L*(1/16:ℝ)^m := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDL (by positivity : 0≤(1/16:ℝ)^m)

/-- The literal finite-block norm mass in a shrinking equality tube has
uniform cubic dyadic decay, enough for the two genuine flux losses. -/
theorem preferred_finite_right_small_mass_of_shells (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ ε₀ : ℝ} (hδB : δB<B.delta)
    (η rcut : ℝ → ℝ) (Nstar k : ℕ) (hNstar : 2≤Nstar) (hk : 2*k+2=Nstar^2)
    (hq28 : PreferredAllDiameterShellBound d B δB τ ε₀ η rcut k)
    (hfinite : PreferredFiniteBlockShellBound d B δB τ ε₀ η rcut Nstar k) :
    ∀ n : ℕ,Nstar+2≤n+1 → n+1≤2*k+4 → Even (n+1) →
    ∀ j : ℕ,j≤k → ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₀ → ∀ m : ℕ,
      (∫⁻ θ : Fin n → ℝ in preferredRightRegion d B δB,
        preferredRightSmallMassIntegrand d B τ η rcut j ε m θ)≤
      ENNReal.ofReal (A*(1+|Real.log ε|)*(1/8:ℝ)^m) := by
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
  have hQ : 4≤Q := higher_order_collision_degree_four hNstar hNl hj hk
  obtain ⟨L,hL,hpowers⟩ := preferred_dyadic_two_power_sixteen_envelope
    (q := shellExponent N j) (Q := Q) hE hD hQ m₀
  refine ⟨6*(N:ℝ)^3*L,by dsimp [N]; positivity,?_⟩
  intro ε hε hεr m
  let H := 1+|Real.log ε|
  have hH : 0≤H := by dsimp [H]; positivity
  have hfull (l : ℕ) (z : ℤ) (i a : Fin N) :
      (∫⁻ θ in preferredRightShell d B δB (preferredDyadicRadius l) z i a,
        ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles θ))‖)≤
      ENNReal.ofReal (L*H*(1/16:ℝ)^l) := by
    have hr := preferredDyadicRadius_pos l
    obtain ⟨hi,hmass⟩ := hshell n (by omega) hEven ε (preferredDyadicRadius l) hε hεr hr z i a
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    change ENNReal.ofReal (preferredRightShellMass d B δB τ η rcut j ε (preferredDyadicRadius l) z i a)=_ at he
    rw [←he]
    apply ENNReal.ofReal_le_ofReal
    by_cases hl : l<m₀
    · have hc := every_diameter_shell_comparison hr
        (preferredShellScale_ge_diameter d N z (preferredDyadicRadius l) hε.le) (by omega : 2≤N) j
      rw [←shell_order_envelope_eq_rpow C J N (by omega)] at hmass
      calc
        _ ≤ E*(preferredDyadicRadius l)^(shellExponent N j)*H :=
          hmass.trans (by simpa only [E,N,H,mul_assoc] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hE) hH)
        _ ≤ (L*(1/16:ℝ)^l)*H := mul_le_mul_of_nonneg_right ((hpowers l).1 hl) hH
        _ = _ := by ring
    · have hl' : m₀≤l := Nat.le_of_not_gt hl
      calc
        _ ≤ D*(preferredDyadicRadius l)^Q*H := hsmall ε (preferredDyadicRadius l)
          hε hεr hr (hm₀ l hl') z i a
        _ ≤ (L*(1/16:ℝ)^l)*H := mul_le_mul_of_nonneg_right ((hpowers l).2 hl') hH
        _ = _ := by ring
  have hb := preferredRightRegion_lintegral_geometric (by omega : 0<n) d B hδB
    (preferredRightSmallMassIntegrand d B τ η rcut j ε m)
    (mul_nonneg (mul_nonneg hL.le hH) (by positivity : 0≤(1/8:ℝ)^m)) ?_
  · simpa only [N,H,mul_assoc] using hb
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
    apply (hdom.trans (hfull l z.1 i a)).trans
    apply ENNReal.ofReal_le_ofReal
    have hshift : (1/16:ℝ)^l≤(1/8:ℝ)^m*(1/2:ℝ)^l := by
      calc
        _ = (1/8:ℝ)^l*(1/2:ℝ)^l := by rw [←mul_pow]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hlm) (by positivity)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hshift (mul_nonneg hL.le hH)
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
