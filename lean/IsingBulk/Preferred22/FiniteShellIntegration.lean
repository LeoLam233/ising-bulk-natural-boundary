import IsingBulk.Preferred22.FiniteShellPowers
import IsingBulk.Preferred22.ShellIntegration
import IsingBulk.Preferred22.ShellScaleBound
import IsingBulk.Preferred22.PhysicalDensityShell

/-! Genuine constrained integration of the full finite-particle
Vandermonde majorant. This isolates the actual scalar factor estimate,
retains every mean and extreme index, and proves integrability independently. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

/-- A literal full-Vandermonde pointwise estimate gives the exact distinct
finite-block shell power. The finite mean gap is explicit; neither an
integrated shell bound nor an integrability assertion is assumed. -/
theorem preferred_finite_vandermonde_shell_bound_regime (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ η rcut : ℝ → ℝ,ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut →
      ∀ n j : ℕ,∀ g D r₀ : ℝ,0<g → 0<D → 0<r₀ →
      (∀ l : ℤ,g≤|preferredShellMean d (n+2) l|) →
      (∀ ε r : ℝ,0<ε → ε<ε₁ → 0<r → r<r₀ → ∀ l : ℤ,∀ i a : Fin (n+2),
        ∀ x∈preferredRightShell d B δB r l i a,
        ‖preferredTransportedDensity .right τ η B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖≤
          (D*(r^((n+2)*(n+1))/r^(2*j)))*
            preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles x))) →
      ∃ E : ℝ,0<E ∧ ∀ ε r : ℝ,0<ε → ε<ε₁ → 0<r → r<r₀ →
      ∀ l : ℤ,∀ i a : Fin (n+2),
      IntegrableOn (fun x => ‖preferredTransportedDensity .right τ η B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖)
        (preferredRightShell d B δB r l i a) ∧
      preferredRightShellMass d B δB τ η rcut j ε r l i a≤
        E*r^(((n+2:ℕ):ℝ)^2-2*(j:ℝ)-3)*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,hintegrable⟩ := preferred_actual_all_order_shell_integrable d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨δi,τi,εi,hδi,hδiδ,hτi,hεi,hi⟩ := hintegrable B hBcap
  obtain ⟨A,C,εc,τc,δc,hA,hC,hεc,hτc,hδc,_hδcδ,hc⟩ :=
    preferred_transported_shell_lintegral d B
  let δ₀ := min δi δc
  let τ₀ := min τi τc
  let ε₀ := min εi (min εc 1)
  refine ⟨δ₀,τ₀,ε₀,lt_min hδi hδc,(min_le_left _ _).trans_lt hδiδ,
    lt_min hτi hτc,lt_min hεi (lt_min hεc (by norm_num)),?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr _hε₁ hε₁₀ η rcut hη hrcut n j g D r₀ hg hD _hr₀ hmean hpoint
  let S := max 1 (Real.sqrt (5*Real.pi+1))
  let E := D*A^n*C*((n+2:ℕ):ℝ)*S*(32/Real.sqrt g)^n
  have hS : 0<S := zero_lt_one.trans_le (le_max_left _ _)
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨E,hE,?_⟩
  intro ε r hε hεr₁ hr hrr l i a
  have hεr : ε<ε₀ := hεr₁.trans_le hε₁₀
  have hεi' : ε<εi := hεr.trans_le (min_le_left _ _)
  have hεc' : ε<εc := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε≤1 := (hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hτi' : τ<τi := hτr.trans_le (min_le_left _ _)
  have hτc' : τ<τc := hτr.trans_le (min_le_right _ _)
  have hδBi : δB≤δi := hδB₀.trans (min_le_left _ _)
  have hδBc : δB≤δc := hδB₀.trans (min_le_right _ _)
  have hδBδ : δB<B.delta := hδBi.trans_lt hδiδ
  have hint := (hi (n+1) (by omega) ε τ hε hεi' hτ hτi' η rcut hη hrcut j r hr l i a).mono_set
    (preferredRightShell_mono_margin d B hδBi l i a)
  refine ⟨hint.norm,?_⟩
  by_cases hnonempty : (preferredRightShell d B δB r l i a).Nonempty
  · obtain ⟨x,hx⟩ := hnonempty
    let T := preferredShellScale d (n+2) l r ε
    let H := 1+|Real.log ε|
    let Q := D*(r^((n+2)*(n+1))/r^(2*j))
    have hT : 0<T := hr.trans_le (preferredShellScale_ge_diameter d (n+2) l r hε.le)
    have hgT : g≤T := by
      have hh := hmean l
      dsimp [T,preferredShellScale]
      linarith
    have hTS : Real.sqrt T≤S := preferredRightShell_sqrt_scale_upper d B hδBδ hε1 hx
    have hQ : 0≤Q := by dsimp [Q]; positivity
    have hH : 0≤H := by dsimp [H]; positivity
    have hl := hc n j ε τ r δB Q hε hεc' hτ hτc' hr hδB hδBc hQ η rcut l i a
      (hpoint ε r hε hεr₁ hr hrr l i a)
    have hp := finite_vandermonde_shell_envelope hA hC hD hg hS n j hr hT hH hgT hTS
    have hb := hl.trans (ENNReal.ofReal_le_ofReal hp)
    have he : ENNReal.ofReal (preferredRightShellMass d B δB τ η rcut j ε r l i a)=
        ∫⁻ x in preferredRightShell d B δB r l i a,
          ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
            (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖ :=
      ofReal_integral_eq_lintegral_ofReal hint.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    rw [←he] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  · have he : preferredRightShell d B δB r l i a=∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [preferredRightShellMass,he,MeasureTheory.setIntegral_empty]
    positivity

/-- Original fixed-threshold specialization of the shrinkable regime. -/
theorem preferred_finite_vandermonde_shell_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ →
      ∀ η rcut : ℝ → ℝ,ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut →
      ∀ n j : ℕ,∀ g D r₀ : ℝ,0<g → 0<D → 0<r₀ →
      (∀ l : ℤ,g≤|preferredShellMean d (n+2) l|) →
      (∀ ε r : ℝ,0<ε → ε<ε₀ → 0<r → r<r₀ → ∀ l : ℤ,∀ i a : Fin (n+2),
        ∀ x∈preferredRightShell d B δB r l i a,
        ‖preferredTransportedDensity .right τ η B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖≤
          (D*(r^((n+2)*(n+1))/r^(2*j)))*
            preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles x))) →
      ∃ E : ℝ,0<E ∧ ∀ ε r : ℝ,0<ε → ε<ε₀ → 0<r → r<r₀ →
      ∀ l : ℤ,∀ i a : Fin (n+2),
      IntegrableOn (fun x => ‖preferredTransportedDensity .right τ η B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖)
        (preferredRightShell d B δB r l i a) ∧
      preferredRightShellMass d B δB τ η rcut j ε r l i a≤
        E*r^(((n+2:ℕ):ℝ)^2-2*(j:ℝ)-3)*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := preferred_finite_vandermonde_shell_bound_regime d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,hreg⟩ := hsource B hBcap
  refine ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,?_⟩
  intro δB τ hδB hδB₀ hτ hτr
  exact hreg δB τ ε₀ hδB hδB₀ hτ hτr hε₀ le_rfl

end
end IsingBulk.Preferred22
