import IsingBulk.Preferred22.VandermondeScale
import IsingBulk.Preferred22.PhysicalJacobianBound
import IsingBulk.Preferred22.PhysicalTransportIteration
import IsingBulk.Preferred22.FiniteShellIntegration
import IsingBulk.Preferred22.FiniteMeanSeparation

/-! The distinct finite intermediate block on the actual source. Full
squared Vandermonde transport, exact physical Piola factorization, the genuine
finite constrained-mean gap, and occupancy coarea are composed without an
assumed pointwise or integrated finite-block bound. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff

/-- The exact finite-order source scalar estimate, distinct from any
integrated shell or tail bound. The unconditional source theorem supplies it. -/
def PreferredFullVandermondeSourceBound (d : PreferredBranchData) : Prop :=
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ ε₀ τ₀ δ₀ : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
        ∀ δB : ℝ, 0<δB → δB≤δ₀ →
        ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
        ∀ j n : ℕ, 0<n → ∃ C : ℝ, 0<C ∧
        ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin (2*n) → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        ‖preferredRegularTransportedScalar τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          C/preferredAngularDiameter θ^(2*j)*
            ‖preferredSquaredVandermonde (preferredSourceCoordinate τ B.p B.m
              (IsingBulk.Branch.radialParameter d.alpha ε) θ)‖

/-- The actual finite-block shell theorem, on a common shrinkable regime.
Every integer constrained mean is present; no all-order Diophantine condition
or finite-block envelope is assumed. -/
theorem preferred_finite_block_shell_bound_of_full_vandermonde (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a)
    (hV : PreferredFullVandermondeSourceBound d) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut → ∀ Nstar k : ℕ,
      PreferredFiniteBlockShellBound d B δB τ ε₁ preferredPopulationCutoff rcut Nstar k := by
  obtain ⟨cv,hcv,hcva,hv⟩ := hV
  obtain ⟨cf,hcf,_hcfa,hf⟩ := preferred_actual_all_order_factorization d
  obtain ⟨ci,hci,_hcia,hi⟩ := preferred_finite_vandermonde_shell_bound_regime d
  refine ⟨min cv (min cf ci),lt_min hcv (lt_min hcf hci),(min_le_left _ _).trans_lt hcva,?_⟩
  intro B hBcap
  obtain ⟨εv,τv,δv,hεv,hτv,hδv,hδvδ,hscalar⟩ := hv B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δf,τf,εf,hδf,_hδfδ,hτf,hεf,hfactor⟩ :=
    hf B (hBcap.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨δi,τi,εi,hδi,_hδiδ,hτi,hεi,hintegral⟩ :=
    hi B (hBcap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Cq,εq,τq,δq,hCq,hεq,hτq,hδq,_hδqδ,hvand⟩ := preferred_actual_finite_vandermonde_scale d B
  obtain ⟨M,εM,hM,hεM,hJH⟩ := preferred_actual_JH_bound d B
  let δ₀ := min δv (min δf (min δi δq))
  let τ₀ := min τv (min τf (min τi (min τq 1)))
  let ε₀ := min εv (min εf (min εi (min εq εM)))
  have hδ₀ : 0<δ₀ := lt_min hδv (lt_min hδf (lt_min hδi hδq))
  have hτ₀ : 0<τ₀ := lt_min hτv (lt_min hτf (lt_min hτi (lt_min hτq (by norm_num))))
  have hε₀ : 0<ε₀ := lt_min hεv (lt_min hεf (lt_min hεi (lt_min hεq hεM)))
  refine ⟨δ₀,τ₀,ε₀,hδ₀,(min_le_left _ _).trans_lt hδvδ,hτ₀,hε₀,?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr hε₁ hε₁₀ rcut hcut Nstar k
  have hδs : δB≤δv ∧ δB≤δf ∧ δB≤δi ∧ δB≤δq := by
    simpa only [δ₀,le_min_iff] using hδB₀
  have hτs : τ<τv ∧ τ<τf ∧ τ<τi ∧ τ<τq ∧ τ<1 := by
    simpa only [τ₀,lt_min_iff] using hτr
  have hεs : ε₁≤εv ∧ ε₁≤εf ∧ ε₁≤εi ∧ ε₁≤εq ∧ ε₁≤εM := by
    simpa only [ε₀,le_min_iff] using hε₁₀
  obtain ⟨g,hg,hmean⟩ := preferred_finite_mean_separation d hp ha hα (by omega : 0<2*k+4)
  refine ⟨1,zero_lt_one,?_⟩
  intro n hNl hNu hEven j _hj
  cases n with
  | zero => omega
  | succ n =>
    have hN : 2≤n+2 := by omega
    have hEven' : Even (n+2) := by simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hEven
    have hscalarN : ∃ Cv : ℝ,0<Cv ∧ ∀ ε : ℝ,0<ε → ε<ε₁ →
        ∀ θ : Fin (n+2) → ℝ,θ∈preferredRightAngularBox d B.delta δB (n+2) →
        0<preferredAngularDiameter θ →
        ‖preferredRegularTransportedScalar τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤
          Cv/preferredAngularDiameter θ^(2*j)*
            ‖preferredSquaredVandermonde (preferredSourceCoordinate τ B.p B.m
              (IsingBulk.Branch.radialParameter d.alpha ε) θ)‖ := by
      obtain ⟨v,hv⟩ := hEven'
      have hNv : n+2=2*v := by omega
      have hv0 : 0<v := by omega
      obtain ⟨Cv,hCv,hc⟩ := hscalar δB hδB hδs.1 rcut hcut.2.2.1 hcut.2.2.2.1 j v hv0
      refine ⟨Cv,hCv,?_⟩
      rw [hNv]
      intro ε hε hεr θ hθ hd
      exact hc ε τ hε (hεr.trans_le hεs.1) hτ hτs.1 θ
        (fun i => ⟨by linarith [(hθ i).1],by linarith [(hθ i).2]⟩) hd
    obtain ⟨Cv,hCv,hc⟩ := hscalarN
    let D := 2*M^(n+2)*Cv*(Cq/Real.sqrt g)^((n+2)*(n+1))
    have hD : 0<D := by dsimp [D]; positivity
    have hpoint : ∀ ε r : ℝ,0<ε → ε<ε₁ → 0<r → r<1 →
        ∀ l : ℤ,∀ i a : Fin (n+2),∀ x∈preferredRightShell d B δB r l i a,
        ‖preferredTransportedDensity .right τ preferredPopulationCutoff B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta (constrainedAngles x))‖≤
        (D*(r^((n+2)*(n+1))/r^(2*j)))*
          preferredJacobianResolvent d B ε τ (preferredLiftedAngles B.delta (constrainedAngles x)) := by
      intro ε r hε hεr hr _hrr l i a x hx
      let θ := preferredLiftedAngles B.delta (constrainedAngles x)
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      have hdiam : r≤preferredAngularDiameter θ := preferredRightShell_diameter_lower d B hr hx
      have hd : 0<preferredAngularDiameter θ := hr.trans_le hdiam
      have hbox : θ∈preferredRightAngularBox d B.delta δB (n+2) := hx.2.1
      have hboxf : θ∈preferredRightAngularBox d B.delta δf (n+2) := fun i =>
        ⟨by linarith [(hbox i).1,hδs.2.1],(hbox i).2⟩
      have hθfull (i : Fin (n+2)) : θ i∈Icc (-Real.pi-B.delta) B.delta :=
        ⟨by linarith [(hbox i).1,hcut.2.1,d.b_lt],(hbox i).2⟩
      have hvand' := hvand δB ε τ r g hδs.2.2.2 hε (hεr.trans_le hεs.2.2.2.1)
        hτ hτs.2.2.2.1 hr hg (n+1) l
        (hmean (n+2) (by omega) (by simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hNu) l) i a x hx
      have hscalar' := hc ε hε hεr θ hbox hd
      have hscalarBound : ‖preferredRegularTransportedScalar τ preferredPopulationCutoff B.p B.m rcut j s θ‖≤
          Cv/r^(2*j)*((Cq/Real.sqrt g)^((n+2)*(n+1))*r^((n+2)*(n+1))) := by
        apply hscalar'.trans
        exact mul_le_mul
          (div_le_div_of_nonneg_left hCv.le (pow_pos hr _) (pow_le_pow_left₀ hr.le hdiam _))
          hvand' (norm_nonneg _) (by positivity)
      have hjh := hJH (n+2) (by omega) ε τ hε (hεr.trans_le hεs.2.2.2.2)
        hτ hτs.2.2.2.2.le θ hθfull
      rw [hfactor (n+2) hN ε τ hε (hεr.trans_le hεs.2.1) hτ hτs.2.1 θ hboxf hd
        preferredPopulationCutoff rcut preferredPopulationCutoff_smooth hcut.2.2.1 j,norm_mul]
      calc
        _ ≤ (2*M^(n+2)*preferredJacobianResolvent d B ε τ θ)*
            (Cv/r^(2*j)*((Cq/Real.sqrt g)^((n+2)*(n+1))*r^((n+2)*(n+1)))) :=
          mul_le_mul hjh hscalarBound (norm_nonneg _) (mul_nonneg (by positivity)
            (preferredJacobianResolvent_nonneg d B ε τ θ))
        _ = _ := by dsimp [D]; ring
    obtain ⟨E,hE,hbound⟩ := hintegral δB τ ε₁ hδB hδs.2.2.1 hτ hτs.2.2.1 hε₁ hεs.2.2.1
      preferredPopulationCutoff rcut preferredPopulationCutoff_smooth hcut.2.2.1 n j g D 1 hg hD zero_lt_one
      (hmean (n+2) (by omega) (by simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hNu)) hpoint
    refine ⟨E,hE,?_⟩
    intro ε r hε hεr hr hrr l i a
    exact (hbound ε r hε hεr hr hrr l i a).2

end
end IsingBulk.Preferred22
