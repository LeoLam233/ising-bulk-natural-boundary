import IsingBulk.Preferred22.ActualAnchorPointwise
import IsingBulk.Preferred22.AnchorIntegralBound
import IsingBulk.Preferred22.PopulationObligations
import IsingBulk.Preferred22.AbsoluteTail

/-! The complete manuscript anchored absolute differentiated estimate,
including the named-anchor sum and the two-particle order. Every source,
transport, profile and normalization premise is discharged. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Manuscript q11 on the actual named-anchor cells. The bump cap is chosen
before B; a fixed positive left separation determines a common parameter
regime before every derivative order and every particle number. -/
theorem preferred_actual_anchor_absolute_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB → δB<B.delta →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ 0<τ₀ ∧
      ∀ τ : ℝ,0≤τ → τ<τ₀ → ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ k : ℕ,PreferredAnchorAbsoluteBound d B τ ε₀ rcut k := by
  obtain ⟨cap,hcap,hcapa,hpoint⟩ := preferred_actual_anchor_pointwise_bound d
  obtain ⟨D,hD,hintegral⟩ := preferred_anchor_integral_profile_bound d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB _hδBB
  obtain ⟨εp,τp,hεp,hτp,hpoint'⟩ := hpoint B hB δB hδB
  obtain ⟨τi,εi,hτi,hεi,hidentity⟩ := preferred_actual_anchor_integral_identity d B
  let ε₀ := min εp (min εi 1)
  let τ₀ := min τp τi
  refine ⟨ε₀,τ₀,lt_min hεp (lt_min hεi zero_lt_one),
    (min_le_right _ _).trans (min_le_right _ _),lt_min hτp hτi,?_⟩
  intro τ hτ hτr rcut hcut k j _hjk
  obtain ⟨C,hC,hbound⟩ := hpoint' rcut hcut j
  refine ⟨C*D,j*j+8*j+1,mul_pos hC hD,?_⟩
  intro n hn he ε hε hεr
  let N := n+1
  have hN : 0<N := by dsimp [N]; omega
  have hε1 : ε≤1 := hεr.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hone (a : Fin (n+1)) :
      ‖iteratedDeriv j (preferredTransportedIntegral (.anchor a) B.delta τ preferredPopulationCutoff B.p B.m rcut 0)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤
        ((C*D)/Real.sqrt N)^N*(N:ℝ)^(j*j+8*j) := by
    rw [hidentity τ hτ (hτr.trans_le (min_le_right _ _)) rcut hcut.2.2.1 hcut.2.2.2.1 n a j ε hε
      (hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _)))]
    have hh := hintegral n hn he ε hε hε1 B τ rcut j (IsingBulk.Branch.radialParameter d.alpha ε) a
      ((C/Real.sqrt N)^N*(N:ℝ)^(j*j+8*j)) (by positivity)
      (fun θ => hbound N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ
        (hτr.trans_le (min_le_left _ _)) (constrainedAngles θ) a j le_rfl)
    exact hh.trans_eq (by dsimp [N]; simp only [mul_pow,div_pow]; ring)
  calc
    _ ≤ ∑ _a : Fin (n+1),((C*D)/Real.sqrt N)^N*(N:ℝ)^(j*j+8*j) := Finset.sum_le_sum (fun a _ => hone a)
    _ = shellOrderEnvelope (C*D) (j*j+8*j+1) N := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,shellOrderEnvelope,pow_succ]
      dsimp [N]
      ring
    _ = _ := shell_order_envelope_eq_rpow (C*D) (j*j+8*j+1) N hN

end
end IsingBulk.Preferred22
