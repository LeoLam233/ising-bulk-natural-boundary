import IsingBulk.Preferred22.FirstFactorDerivativeLog
import IsingBulk.Preferred22.CriticalLocalization
import IsingBulk.Preferred22.ActualAnchorBound
import IsingBulk.Preferred22.SelectedKernelDisk
import IsingBulk.Preferred22.FirstRemainderFTC
import IsingBulk.Preferred22.PrimeBranchData

/-! The first singular coefficient of the complete physical susceptibility.
The actual selected and named-anchor pieces, full right complement, exact
critical chart, radial FTC and nonzero local leading term are all included.
No complete remainder bound is left as a premise. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The complete coefficient minus twice the literal critical local
integral has the all-order logarithmic derivative estimate. The shape
radius can be required to lie inside any prescribed positive radius. -/
theorem preferred_actual_first_remainder_log (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (n : ℕ) (hN : n+1=2*p)
    (Rmax : ℝ) (hRmax : 0<Rmax) :
    ∃ ρ ε₀ : ℝ,0<ρ ∧ ρ≤Rmax ∧ 0<ε₀ ∧ ∀ j : ℕ,∃ C : ℝ,0<C ∧
      ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv j (coefficient (n+1)) (IsingBulk.Branch.radialParameter d.alpha ε)-
          2*iteratedDeriv j (localizedPhysicalIntegral d.alpha (preferredShapeCutoff (n := n) ρ))
            (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C*(1+|Real.log ε|) := by
  obtain ⟨cR,hcR,_hcRa,hright⟩ := preferred_actual_first_regular_factor_derivative_log d hp hp5 ha hα n hN
  obtain ⟨cA,hcA,_hcAa,hanchor⟩ := preferred_actual_anchor_absolute_bound d
  let cap := min cR cA
  have hcap : 0<cap := lt_min hcR hcA
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<cap := cappedCanonicalPreferredBump_delta_lt d hcap
  obtain ⟨δR,τR,εR,hδR,hδRB,hτR,hεR,hright'⟩ := hright B (hB.trans_le (min_le_left _ _))
  let δB := min δR (preferredRightMargin d B)/2
  have hmargin := preferredRightMargin_bounds d B
  have hδB : 0<δB := half_pos (lt_min hδR hmargin.1)
  have hδBR : δB≤δR := by dsimp only [δB]; linarith [min_le_left δR (preferredRightMargin d B)]
  have hδBm : δB≤preferredRightMargin d B := by
    dsimp only [δB]
    linarith [min_le_right δR (preferredRightMargin d B)]
  let rcut := preferredRightCutoff d δB
  have hcut : PreferredRightCutoffData d B δB rcut := preferred_right_cutoff_data_of_le d B hδB hδBm
  obtain ⟨εA,τA,hεA,_hεA1,hτA,hanchor'⟩ :=
    hanchor B (hB.trans_le (min_le_right _ _)) δB hδB (hδBR.trans_lt hδRB)
  obtain ⟨ρS,hρS,_hρS1,hselected⟩ := preferred_actual_selected_finite_orders d hcap
  obtain ⟨ρ,κ,hρ,hρmax,hκ,hψ,hσ,hσb,hσzero,hlocal⟩ :=
    preferred_critical_cutoff_package d B δB rcut hcut n (2*a)
      (preferred_prime_critical_winding d hp.pos hN hα) Rmax hRmax
  let ψ := preferredCriticalMultiplier (n := n) d.alpha ρ
  let σ := fun θ : Fin (n+1) → ℝ => 1-ψ θ
  let τ := min τR (min τA ρS)/2
  have hτ : 0<τ := half_pos (lt_min hτR (lt_min hτA hρS))
  have hτR' : τ<τR := by
    dsimp only [τ]
    linarith [min_le_left τR (min τA ρS)]
  have hτA' : τ<τA := by
    have hh := (min_le_right τR (min τA ρS)).trans (min_le_left τA ρS)
    dsimp only [τ]
    linarith
  have hτρ : τ<ρS := by
    have hh := (min_le_right τR (min τA ρS)).trans (min_le_right τA ρS)
    dsimp only [τ]
    linarith
  let ε₀ := min εR (min εA ρS)
  have hε₀ : 0<ε₀ := lt_min hεR (lt_min hεA hρS)
  have hεR' : ε₀≤εR := min_le_left _ _
  have hεA' : ε₀≤εA := (min_le_right _ _).trans (min_le_left _ _)
  have hερ : ε₀≤ρS := (min_le_right _ _).trans (min_le_right _ _)
  have hN2 : 2≤n+1 := by omega
  have hEven : Even (n+1) := ⟨p,by omega⟩
  refine ⟨ρ,ε₀,hρ,hρmax,hε₀,?_⟩
  intro j
  obtain ⟨CF,hCF,hF⟩ := hselected τ hτ hτρ n hN2 hEven j
  obtain ⟨CA,J,hCA,hA⟩ := hanchor' τ hτ.le hτA' rcut hcut j j le_rfl
  obtain ⟨CR,hCR,hR⟩ := hright' δB hδB hδBR rcut hcut τ hτ.le hτR' σ hσ hσb κ hκ hσzero j
  let KA := CA^(n+1)*((n+1:ℕ):ℝ)^(-((n+1:ℕ):ℝ)/2+(J:ℝ))
  have hKA : 0≤KA := by dsimp only [KA]; positivity
  refine ⟨CF+2*(CR+KA),by positivity,?_⟩
  intro ε hε hεr
  have hFb := hF ε hε (hεr.trans_le hερ)
  have hAb := hA n hN2 hEven ε hε (hεr.trans_le hεA')
  have hRb := hR ε hε (hεr.trans_le hεR')
  let F := iteratedDeriv j (preferredFullPopulationIntegral n τ preferredPopulationCutoff B.p B.m)
    (IsingBulk.Branch.radialParameter d.alpha ε)
  let S := iteratedDeriv j (preferredWeightedRightIntegral n d B σ τ rcut 0)
    (IsingBulk.Branch.radialParameter d.alpha ε)
  let A := fun a : Fin (n+1) => iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ
    preferredPopulationCutoff B.p B.m rcut 0) (IsingBulk.Branch.radialParameter d.alpha ε)
  have he : iteratedDeriv j (coefficient (n+1)) (IsingBulk.Branch.radialParameter d.alpha ε)-
      2*iteratedDeriv j (localizedPhysicalIntegral d.alpha (preferredShapeCutoff (n := n) ρ))
        (IsingBulk.Branch.radialParameter d.alpha ε)=F+2*(S+∑a,A a) := by
    rw [preferred_complete_derivative_partition n hEven d B hτ.le rcut hcut.2.2.1 hcut.2.2.2.1 j hε,
      preferredWeightedRightIntegral_derivative_partition n d B hτ.le ψ hψ rcut hcut.2.2.1 j hε]
    change F+2*(iteratedDeriv j (preferredWeightedRightIntegral n d B ψ τ rcut 0)
      (IsingBulk.Branch.radialParameter d.alpha ε)+S+∑a,A a)-
      2*iteratedDeriv j (localizedPhysicalIntegral d.alpha (preferredShapeCutoff (n := n) ρ))
        (IsingBulk.Branch.radialParameter d.alpha ε)=F+2*(S+∑a,A a)
    rw [hlocal τ]
    ring
  rw [he]
  calc
    _ ≤ ‖F‖+‖(2:ℂ)*(S+∑a,A a)‖ := norm_add_le _ _
    _ = ‖F‖+2*‖S+∑a,A a‖ := by rw [norm_mul]; norm_num
    _ ≤ ‖F‖+2*(‖S‖+∑a,‖A a‖) := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))) (by norm_num))
    _ ≤ CF+2*(CR*(1+|Real.log ε|)+KA) :=
      add_le_add hFb (mul_le_mul_of_nonneg_left (add_le_add hRb hAb) (by norm_num))
    _ ≤ (CF+2*(CR+KA))*(1+|Real.log ε|) := by
      nlinarith [mul_nonneg hCF.le (abs_nonneg (Real.log ε)),
        mul_nonneg hKA (abs_nonneg (Real.log ε))]

/-- The actual bounded remainder is derived by radial FTC, then the
nonzero physical local leading coefficient gives the first singularity. -/
theorem preferred_actual_first_singularity_of_branch (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) (n : ℕ) (hN : n+1=2*p) :
    PreferredFirstSingularityStatement (Complex.exp ((d.alpha:ℂ)*Complex.I))
      (n+1) ((n+1)^2/2-1) := by
  have hn : 1≤n := by omega
  have hEven : Even (n+1) := ⟨p,by omega⟩
  have hres : Complex.exp (-(n+1:ℂ)*(d.alpha:ℂ)*Complex.I)=1 := by
    have hcast : (n+1:ℂ)=((2*p:ℕ):ℂ) := by exact_mod_cast hN
    rw [hcast,hα]
    exact preferred_prime_first_resonance hp.pos a
  obtain ⟨Rs,hRs,hsing⟩ := preferred_first_singularity_of_bounded_remainder hn hEven
    d.alpha d.alpha_pos d.alpha_lt hres
  obtain ⟨Rf,hRf,hFTC⟩ := preferred_first_remainder_of_log_next hEven
    d.alpha d.alpha_pos d.alpha_lt hres
  obtain ⟨ρ,ε₀,hρ,hρmax,hε₀,hlog⟩ := preferred_actual_first_remainder_log d hp hp5 ha hα n hN
    (min Rs Rf) (lt_min hRs hRf)
  apply hsing ρ hρ (hρmax.trans (min_le_left _ _))
  apply hFTC (preferredShapeCutoff ρ) (preferredShapeCutoff_smooth ρ).continuous
    (fun x hx => (preferredShapeCutoff_support hρ x hx).trans_le (hρmax.trans (min_le_right _ _)))
    ((n+1)^2/2-1)
  obtain ⟨C,hC,hb⟩ := hlog (((n+1)^2/2-1)+1)
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro ε hε hεr
  simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hb ε hε hεr

/-- The precise manuscript prime-root first singularity, for the complete
physical coefficient at Nstar=2p and k=(2p)^2/2-1. No remainder assumption,
new axiom or old natural-boundary/tail endpoint occurs in this theorem. -/
theorem preferred_actual_first_singularity {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) :
    PreferredFirstSingularityStatement (IsingBulk.PrimeFamily.angleRoot p a)
      (2*p) ((2*p)^2/2-1) := by
  have hN : 2*p-1+1=2*p := by omega
  have hh := preferred_actual_first_singularity_of_branch (preferredPrimeBranchData ha)
    hp hp5 ha rfl (2*p-1) hN
  simpa only [hN,preferredPrimeBranchData,preferredBranchAt,IsingBulk.PrimeFamily.angleRoot] using hh

end
end IsingBulk.Preferred22
