import IsingBulk.Preferred22.RightRadialTransport
import IsingBulk.Preferred22.CompleteRightPuncture
import IsingBulk.Preferred22.CompleteRightDerivativeTail

/-! Exact right transport through the distinct finite intermediate block
and the entire infinite tail. Both use the same actual punctured Stokes
identity and common physical source regime. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Every actual even order above the first singular order has the exact
original right integral transport identity. All physical shell, finite
collision-degree, current, smoothness and tangency inputs are discharged. -/
theorem preferred_actual_complete_right_integral_identity (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ Nstar k : ℕ,2≤Nstar → Even Nstar → 2*k+2=Nstar^2 →
      PreferredRightIntegralIdentity d B τ ε₁ rcut Nstar k := by
  obtain ⟨cp,hcp,hcpa,hcontrol⟩ := preferred_actual_complete_right_puncture_control d hp ha hα
  obtain ⟨cg,hcg,_hcga,hg⟩ := preferred_actual_regularDomain d
  obtain ⟨ct,hct,_hcta,ht⟩ := preferred_actual_right_tangency d
  let cap := min cp (min cg ct)
  refine ⟨cap,lt_min hcp (lt_min hcg hct),(min_le_left _ _).trans_lt hcpa,?_⟩
  intro B hBcap
  obtain ⟨δp,τp,εp,hδp,hδpδ,hτp,hεp,hcontrol'⟩ :=
    hcontrol B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δg,τg,εg,hδg,_hδgδ,hτg,hεg,hg'⟩ :=
    hg B (hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨δt,τt,εt,hδt,_hδtδ,hτt,hεt,ht'⟩ :=
    ht B (hBcap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  let δ₀ := min δp (min δg δt)
  let τ₀ := min τp (min τg τt)
  let ε₀ := min εp (min εg εt)
  refine ⟨δ₀,τ₀,ε₀,lt_min hδp (lt_min hδg hδt),(min_le_left _ _).trans_lt hδpδ,
    lt_min hτp (lt_min hτg hτt),lt_min hεp (lt_min hεg hεt),?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr hε₁ hε₁₀ rcut hcut Nstar k hNstar hEvenStar hk n hN hEven
  have hδp' : δB≤δp := hδB₀.trans (min_le_left _ _)
  have hδg' : δB≤δg := hδB₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδt' : δB≤δt := hδB₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτp' : τ<τp := hτr.trans_le (min_le_left _ _)
  have hτg' : τ<τg := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτt' : τ<τt := hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hεp' : ε₁≤εp := hε₁₀.trans (min_le_left _ _)
  have hεg' : ε₁≤εg := hε₁₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεt' : ε₁≤εt := hε₁₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNl : Nstar+2≤n+1 := by
    obtain ⟨u,hu⟩ := hEvenStar
    obtain ⟨v,hv⟩ := hEven
    omega
  have hreg : ∀ ε∈Ioo 0 ε₁,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (IsingBulk.Branch.radialParameter d.alpha ε,x)∈preferredPhysicalRegularDomain τ B.p B.m := by
    intro ε hε x hx hd
    apply hg' (n+1) (by omega) ε τ hε.1 (hε.2.trans_le hεg') hτ hτg' x _ hd
    intro i
    exact ⟨by linarith [(hx i).1],(hx i).2⟩
  have htan : ∀ ε∈Ioo 0 ε₁,∀ x∈preferredRightAngularBox d B.delta δB (n+1),
      0<preferredAngularDiameter x →
      (∑ i,preferredSourceAngularField .right τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x i)=0 := by
    intro ε hε x hx hd
    apply ht' (n+1) (by omega) ε τ hε.1 (hε.2.trans_le hεt') hτ hτt' x _ hd
    intro i
    exact ⟨by linarith [(hx i).1],(hx i).2⟩
  have hcontrols := hcontrol' δB τ ε₁ hδB hδp' hτ hτp' hε₁ hεp' rcut hcut Nstar k hNstar hk n hNl hEven
  have hderiv : ∀ j : ℕ,j<k → ∀ ε : ℝ,ε∈Ioo 0 ε₁ →
      HasDerivAt (preferredRightRadialIntegral n d B τ rcut j)
        (Complex.exp ((d.alpha:ℂ)*Complex.I)*preferredRightRadialIntegral n d B τ rcut (j+1) ε) ε := by
    intro j hj ε hε
    apply preferred_right_radial_hasDerivAt_of_puncture_estimates d B rcut hcut hreg htan ?_ ?_ hε
    · intro l hl
      obtain ⟨A,hA,herr⟩ := (hcontrols l (by omega)).1
      exact ⟨A,hA,fun e he m => ((herr e he.1 he.2).2 m).2⟩
    · obtain ⟨L,hL,herr⟩ := (hcontrols j (by omega)).2
      exact ⟨L,hL,fun e he m => herr e he.1 he.2 m⟩
  intro j hj ε hε hεr
  exact preferred_right_iterated_integral_of_radial_derivatives n d B hτ rcut hcut.2.2.1 hcut.2.2.2.1
    k hderiv j hj ε ⟨hε,hεr⟩

end
end IsingBulk.Preferred22
