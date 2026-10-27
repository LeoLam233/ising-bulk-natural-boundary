import IsingBulk.Preferred22.WordSourceBound
import IsingBulk.Preferred22.TransportShellPowers
import IsingBulk.Preferred22.ShellScaleBound
import IsingBulk.Preferred22.PhysicalDensityShell
import IsingBulk.Preferred22.ShellIntegration

/-! Exact application of the normalized scalar-word bound to all actual
right shells. No assumed integrated tail or differentiated determinant bound
enters: the literal physical density, Piola identity, marked minors,
Jacobian/resolvent coarea and shell measure are already proved. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal

/-- The true remaining scalar coefficient estimate implies the manuscript's
complete all-diameter q28, on the literal transported physical density.
The domain and coarea constants precede k,N,epsilon,r,means and extrema.
Integrability is proved independently from the actual open physical domain. -/
theorem preferred_all_diameter_shell_bound_of_normalized_words (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ η rcut : ℝ → ℝ,ContDiff ℝ ∞ η → ContDiff ℝ ∞ rcut → ∀ k : ℕ,
      PreferredNormalizedWordBound d B δB τ ε₁ η rcut k →
      PreferredAllDiameterShellBound d B δB τ ε₁ η rcut k := by
  obtain ⟨cs,hcs,hcsa,hsource⟩ := preferred_actual_word_source_majorant d
  obtain ⟨ci,hci,_hcia,hintegrable⟩ := preferred_actual_all_order_shell_integrable d
  let cap := min cs ci
  refine ⟨cap,lt_min hcs hci,(min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  obtain ⟨K,M,εs,τs,δs,hK,hM,hεs,hτs,hδs,hδsδ,hs⟩ :=
    hsource B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δi,τi,εi,hδi,_hδiδ,hτi,hεi,hi⟩ :=
    hintegrable B (hBcap.trans_le (min_le_right _ _))
  obtain ⟨A,Cc,εc,τc,δc,hA,hCc,hεc,hτc,hδc,_hδcδ,hc⟩ :=
    preferred_transported_shell_lintegral d B
  let δ₀ := min δs (min δi δc)
  let τ₀ := min τs (min τi τc)
  let ε₀ := min εs (min εi (min εc 1))
  have hδ₀ : 0<δ₀ := lt_min hδs (lt_min hδi hδc)
  have hδ₀δ : δ₀<B.delta := (min_le_left _ _).trans_lt hδsδ
  have hτ₀ : 0<τ₀ := lt_min hτs (lt_min hτi hτc)
  have hε₀ : 0<ε₀ := lt_min hεs (lt_min hεi (lt_min hεc (by norm_num)))
  refine ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr _hε₁ hε₁₀ η rcut hη hrcut k hwords j hj
  obtain ⟨C,J,hC,hcoeff⟩ := hwords j hj
  let S := max 1 (Real.sqrt (5*Real.pi+1))
  let D := (2*S)^j*M*(C*K*Real.exp 1)
  have hS : 1≤S := le_max_left _ _
  have hD : 0<D := by dsimp [D]; positivity
  obtain ⟨E,hE,hpowers⟩ := transported_shell_q28_envelope hA hCc hD (J+2*j) j
  refine ⟨E,J+2*j+1,hE,?_⟩
  intro n hN _hEven ε r hε hεr hr l i a
  have hεsmall : ε<ε₀ := hεr.trans_le hε₁₀
  have hεs' : ε<εs := hεsmall.trans_le (min_le_left _ _)
  have hεi' : ε<εi := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεc' : ε<εc := hεsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε1 : ε≤1 := (hεsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hτs' : τ<τs := hτr.trans_le (min_le_left _ _)
  have hτi' : τ<τi := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτc' : τ<τc := hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδBs : δB≤δs := hδB₀.trans (min_le_left _ _)
  have hδBi : δB≤δi := hδB₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδBc : δB≤δc := hδB₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδBδ : δB<B.delta := hδB₀.trans_lt hδ₀δ
  have hint := (hi n hN ε τ hε hεi' hτ hτi' η rcut hη hrcut j r hr l i a).mono_set
    (preferredRightShell_mono_margin d B hδBi l i a)
  refine ⟨hint.norm,?_⟩
  cases n with
  | zero => omega
  | succ m =>
    let T := preferredShellScale d (m+2) l r ε
    let H := 1+|Real.log ε|
    let Q := 2*shellOrderEnvelope D (J+2*j) (m+2)*(r^(m+2)/(r^(2*j)*(Real.sqrt T)^(m+2)))
    have hT : 0<T := hr.trans_le (preferredShellScale_ge_diameter d (m+2) l r hε.le)
    have hH : 0≤H := by dsimp [H]; positivity
    have hQ : 0≤Q := by dsimp [Q,shellOrderEnvelope]; positivity
    have hpoint (x : Fin (m+1) → ℝ) (hx : x∈preferredRightShell d B δB r l i a) :
        ‖preferredTransportedDensity .right τ η B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖≤
          Q*preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles x)) := by
      let w := preferredLiftedAngles B.delta (constrainedAngles x)
      have hbox (v : Fin (m+2)) : -δs≤w v+d.b ∧ w v+d.b≤d.b+B.delta := by
        have hh := hx.2.1 v
        constructor <;> linarith [hh.1,hh.2]
      have hboxB : w∈preferredRightAngularBox d B.delta δB (m+2) := hx.2.1
      have hrD := preferredRightShell_diameter_lower d B hr hx
      have hdiam : 0<preferredAngularDiameter w := hr.trans_le hrD
      have hscale := preferredRightShell_sqrt_scale_upper d B hδBδ hε1 hx
      have hbound := hs (m+2) (by omega) ε τ (preferredShellMean d (m+2) l) r S
        hε hεs' hτ hτs' hr hS hscale w hbox (preferredRightShell_window d B hx) hrD
        η rcut hη hrcut j J C hC (hcoeff (m+2) (by omega) ε hε hεr w hboxB hdiam)
      simpa only [Q,D,T,preferredShellScale,w] using hbound
    have hl := hc m j ε τ r δB Q hε hεc' hτ hτc' hr hδB hδBc hQ η rcut l i a hpoint
    have hp := hpowers m r T H hr hT hH
    have hb := hl.trans (ENNReal.ofReal_le_ofReal hp)
    have he : ENNReal.ofReal (preferredRightShellMass d B δB τ η rcut j ε r l i a)=
        ∫⁻ x in preferredRightShell d B δB r l i a,
          ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
            (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖ :=
      ofReal_integral_eq_lintegral_ofReal hint.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    rw [← he] at hb
    have hR : 0≤E^(m+2)*((m+2:ℕ):ℝ)^(-((m+2:ℕ):ℝ)/2+((J+2*j+1:ℕ):ℝ))*
        r^(2*((m+2:ℕ):ℝ)-2*(j:ℝ)-3)*T^(-((m+2:ℕ):ℝ)+3/2)*H := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff hR).mp hb

end
end IsingBulk.Preferred22
