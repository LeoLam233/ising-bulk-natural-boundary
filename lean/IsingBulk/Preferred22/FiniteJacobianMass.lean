import IsingBulk.Preferred22.FiniteComplementMass
import IsingBulk.Preferred22.ShellIntegration
import IsingBulk.Preferred22.ShellScaleBound

/-! Complete finite-particle integration of the actual Jacobian/resolvent
outside any fixed equality tube. The mean, extrema, affine lift and all
remaining shell measures are retained. The resulting bound applies to the
literal smoothly weighted transport descendants. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

theorem preferred_general_shell_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n : ℕ, ∀ ε τ r δB K : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → 0 ≤ K → ∀ f : (Fin (n+2) → ℝ) → ℝ,
      ∀ l : ℤ, ∀ i j : Fin (n+2),
      (∀ x ∈ preferredRightShell d B δB r l i j,
        f (preferredLiftedAngles B.delta (constrainedAngles x)) ≤
        K*preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles x))) →
      (∫⁻ x in preferredRightShell d B δB r l i j,
        ENNReal.ofReal (f (preferredLiftedAngles B.delta (constrainedAngles x)))) ≤
      ENNReal.ofReal (K*(A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt (preferredShellScale d (n+2) l r ε)/r*(1+|Real.log ε|))*
        (32*r/Real.sqrt (preferredShellScale d (n+2) l r ε))^n)) := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hq⟩ := preferred_shell_q20_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro n ε τ r δB K hε hεr hτ hτr hr hδB hδ hK f l i j hpoint
  have hδδ : δB<B.delta := hδ.trans_lt hδ₀δ
  let c := 2*Real.pi*(l:ℝ)
  have hb : ∀ x : Fin (n+1) → ℝ, constrainedAtTotal c x∈preferredFullRightShell d B δB r i j →
      f (constrainedAtTotal c x) ≤ K*preferredJacobianResolvent d B ε τ (constrainedAtTotal c x) := by
    intro x hx
    have hl : x∈preferredLinearRightShell d B δB r l i j := hx
    have hs : x∈preferredRightShell d B δB r l i j := by
      rw [preferredRightShell_eq_linear d B hδδ]
      exact hl
    have he := (preferred_lift_eq_affine_from_right d B hδδ l x hl.1).2
    simpa only [he] using hpoint x hs
  have hh := hq n ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK i j f hb
  calc
    _ = ∫⁻ x in preferredLinearRightShell d B δB r l i j,
        ENNReal.ofReal (f (constrainedAtTotal c x)) := by
      rw [preferredRightShell_eq_linear d B hδδ]
      apply setLIntegral_congr_fun (preferredLinearRightShell_isClosed d B δB r l i j).measurableSet
      intro x hx
      dsimp only
      rw [(preferred_lift_eq_affine_from_right d B hδδ l x hx.1).2]
    _ = ∫⁻ x : Fin (n+1) → ℝ,
        (preferredFullRightShell d B δB r i j).indicator (fun w => ENNReal.ofReal (f w))
          (constrainedAtTotal c x) := by
      rw [← lintegral_indicator (preferredLinearRightShell_isClosed d B δB r l i j).measurableSet]
      apply lintegral_congr
      intro x
      by_cases hx : x∈preferredLinearRightShell d B δB r l i j
      · have hx' : constrainedAtTotal c x∈preferredFullRightShell d B δB r i j := hx
        rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx']
      · have hx' : constrainedAtTotal c x∉preferredFullRightShell d B δB r i j := hx
        rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem hx']
    _ ≤ _ := by simpa only [preferredShellScale,preferredShellMean] using hh


def preferredAwayJacobian {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (ε τ ρ : ℝ) (θ : Fin n → ℝ) : ℝ≥0∞ :=
  if ρ≤preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles θ)) then
    ENNReal.ofReal (preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles θ)))
  else 0

/-- True integration of the fixed-diameter complement of the physical
resolvent. Constants precede epsilon and all allowed contour heights; no
full-tail, density or shell premise appears. -/
theorem preferred_finite_away_jacobian_mass (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀δB : ℝ,0<δB→δB≤δ₀→∀n : ℕ,∀ρ : ℝ,0<ρ→
      ∃L : ℝ,0<L ∧ ∀ε τ : ℝ,0<ε→ε<ε₀→0≤τ→τ<τ₀→
        (∫⁻ θ : Fin (n+1) → ℝ in preferredRightRegion d B δB,
          preferredAwayJacobian d B ε τ ρ θ)≤ENNReal.ofReal (L*(1+|Real.log ε|)) := by
  obtain ⟨A,C,εc,τ₀,δ₀,hA,hC,hεc,hτ₀,hδ₀,hδ₀δ,hjac⟩ := preferred_general_shell_lintegral d B
  refine ⟨δ₀,τ₀,min εc 1,hδ₀,hδ₀δ,hτ₀,lt_min hεc (by norm_num),?_⟩
  intro δB hδB hδB₀ n ρ hρ
  have hδδ : δB<B.delta := hδB₀.trans_lt hδ₀δ
  let S := max 1 (Real.sqrt (5*Real.pi+1))
  let E := A^n*C*((n+2:ℕ):ℝ)*S*(32*S)^n
  have hS : 0<S := zero_lt_one.trans_le (le_max_left _ _)
  have hE : 0≤E := by dsimp [E]; positivity
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp
    (preferredDyadicRadius_tendsto_zero.eventually (gt_mem_nhds (half_pos hρ)))
  obtain ⟨L,hL,hpow⟩ := preferred_dyadic_two_power_envelope
    (q:=(-1:ℝ)) (Q:=1) hE zero_lt_one le_rfl m₀
  refine ⟨6*((n+2:ℕ):ℝ)^3*L,by positivity,?_⟩
  intro ε τ hε hεr hτ hτr
  have hεc' : ε<εc := hεr.trans_le (min_le_left _ _)
  have hε1 : ε≤1 := (hεr.trans_le (min_le_right _ _)).le
  let H := 1+|Real.log ε|
  have hH : 0≤H := by dsimp [H]; positivity
  have hb := preferredRightRegion_lintegral_geometric (by omega : 0<n+1) d B hδδ
    (preferredAwayJacobian d B ε τ ρ) (mul_nonneg hL.le hH) ?_
  · simpa only [H,mul_assoc] using hb
  intro m l i a
  let r := preferredDyadicRadius m
  have hr : 0<r := preferredDyadicRadius_pos m
  have hmeas : MeasurableSet (preferredRightShell d B δB r l.1 i a) := by
    rw [preferredRightShell_eq_linear d B hδδ]
    exact (preferredLinearRightShell_isClosed d B δB r l.1 i a).measurableSet
  by_cases hm : m<m₀
  · by_cases hnonempty : (preferredRightShell d B δB r l.1 i a).Nonempty
    · obtain ⟨x,hx⟩ := hnonempty
      let T := preferredShellScale d (n+2) l.1 r ε
      have hrT : r≤T := preferredShellScale_ge_diameter d (n+2) l.1 r hε.le
      have hT : 0<T := hr.trans_le hrT
      have hsq : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
      have hTS : Real.sqrt T≤S := preferredRightShell_sqrt_scale_upper d B hδδ hε1 hx
      have hratio : 32*r/Real.sqrt T≤32*S := by
        apply (div_le_iff₀ hsq).mpr
        calc
          32*r ≤ 32*T := mul_le_mul_of_nonneg_left hrT (by norm_num)
          _ = 32*(Real.sqrt T)^2 := by rw [Real.sq_sqrt hT.le]
          _ ≤ 32*S*Real.sqrt T := by nlinarith [mul_le_mul_of_nonneg_right hTS hsq.le]
      have hdom : (∫⁻ θ in preferredRightShell d B δB r l.1 i a,
          preferredAwayJacobian d B ε τ ρ θ)≤
          ∫⁻ θ in preferredRightShell d B δB r l.1 i a,
            ENNReal.ofReal (preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles θ))) := by
        apply lintegral_mono
        intro θ
        unfold preferredAwayJacobian
        split_ifs <;> simp
      have hj := hjac n ε τ r δB 1 hε hεc' hτ hτr hr hδB hδB₀ (by norm_num)
        (preferredJacobianResolvent d B ε τ) l.1 i a (by intro θ _; simp)
      have hbound :
          1*(A^n*(C*((n+2:ℕ):ℝ)*Real.sqrt T/r*H)*(32*r/Real.sqrt T)^n)≤
            E*r^(-1:ℝ)*H := by
        rw [one_mul,Real.rpow_neg_one]
        calc
          _ ≤ A^n*(C*((n+2:ℕ):ℝ)*S/r*H)*(32*S)^n := by
            gcongr
          _ = _ := by dsimp [E]; ring
      have hp := (hpow m).1 hm
      have hlast : E*r^(-1:ℝ)*H≤(L*H)*(1/2:ℝ)^m := by
        calc
          _ ≤ (L*(1/2:ℝ)^m)*H := mul_le_mul_of_nonneg_right hp hH
          _ = _ := by ring
      exact (hdom.trans hj).trans (ENNReal.ofReal_le_ofReal (hbound.trans hlast))
    · have he : preferredRightShell d B δB r l.1 i a=∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
      rw [he,Measure.restrict_empty,lintegral_zero_measure]
      exact bot_le
  · have hsmall := hm₀ m (Nat.le_of_not_gt hm)
    have hz (θ : Fin (n+1) → ℝ) (hθ : θ∈preferredRightShell d B δB r l.1 i a) :
        preferredAwayJacobian d B ε τ ρ θ=0 := by
      unfold preferredAwayJacobian
      apply ite_eq_right
      have hd := preferredRightShell_diameter_upper d B hr hθ
      dsimp only [r] at hd
      linarith
    rw [setLIntegral_congr_fun hmeas hz,lintegral_zero]
    exact bot_le

end
end IsingBulk.Preferred22
