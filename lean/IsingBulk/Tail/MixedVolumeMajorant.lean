import IsingBulk.Tail.MixedSpectatorMajorant
import IsingBulk.Tail.MixedSourcePlateaus
import IsingBulk.Tail.SectorPartitionSupport
import IsingBulk.Tail.MixedHybridDensity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators

theorem mixedHybridVolume_spectator_bound {N : ℕ} (J : Finset (Fin N))
    (j q : Fin N) (hj : j∈J) (hq : q∉J) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (L : ℝ → ℝ)
    (hL : ∀ t,1≤L t)
    (hbound : ∀ i∈J.erase j,‖mixedSourceSlope s (deformedPoint f r τ lam θ i)‖≤L (θ i)) :
    ‖mixedHybridVolume J f r τ lam s θ‖≤
      ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
        ∏ i∈(Finset.univ.erase j).erase q,L (θ i) := by
  classical
  rw [mixedHybridVolume,← Finset.mul_prod_erase J _ hj,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hbound).trans
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro i hi
    exact Finset.mem_erase.mpr ⟨fun hiq => hq (hiq ▸ (Finset.mem_erase.mp hi).2),
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1,Finset.mem_univ _⟩⟩
  · exact fun i _ => zero_le_one.trans (hL (θ i))
  · exact fun i _ _ => hL (θ i)

/-- The actual original/current source supports furnish every branch
spectator majorant. The constants preceding eta and alpha are dimension
independent and the remaining coordinates need no sector subdivision. -/
theorem mixed_actual_source_volume_majorant (d : LocalBranchData) :
    ∃ B e t₀ : ℝ,0<B ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∃ inner₀ : ℝ,0< inner₀ ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (J : Finset (Fin N)) (j q : Fin N),
      0<N → 0<eps → eps<e → 0≤τ → τ<t₀ → 0≤lam → lam≤1 →
      θ∈angleBox N → j∈J → q∉J →
      (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
        θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q)) →
      (∀ i∈J,θ i∈tsupport (sectorBranch d.thetaB inner hi)) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      ‖mixedHybridVolume J f r τ lam s θ‖≤
        ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
          ∏ i∈(Finset.univ.erase j).erase q,mixedSpectatorMajorant d.thetaB B eps (θ i) := by
  obtain ⟨B,R,t₀,hB,hR,ht,hBound⟩ := mixed_actual_branch_slope_majorant d
  refine ⟨B,R,t₀,hB,hR,ht,?_⟩
  intro η α hη hηsmall hα hαsmall
  obtain ⟨i₀,hi₀,hwidth⟩ := sector_branch_support_lower_chart d.thetaB_pos d.thetaB_lt
    (lt_min hR (half_pos hη))
  refine ⟨i₀,hi₀,?_⟩
  intro inner hi hinner N eps τ lam θ J j q hN he heR hτ hτlt hl0 hl1 hbox hj hq hSource hBranch
  apply mixedHybridVolume_spectator_bound J j q hj hq _ _ _ _ _ θ _
    (mixedSpectatorMajorant_one_le d.thetaB hB.le)
  intro i hiJ
  have hiJ' := (Finset.mem_erase.mp hiJ).2
  have hsin : Real.sin (θ i)≤3*α/2 := by
    rcases hSource with hO | hC
    · exact constructed_original_support_sine_upper d.thetaB η α hα i hO
    · exact constructed_current_support_sine_upper d.thetaB η α hα q i hC
  have hu := hwidth inner hi hinner (θ i) (hbox.1 i) (hbox.2 i)
    (show Real.sin (θ i)≤Real.sin d.thetaB/2 by linarith [d.a_pos]) (hBranch i hiJ')
  have hcore : lowerChord d.thetaB (θ i)<η^2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (hu.le.trans (min_le_right _ _)) 2
    rw [sq_abs] at hs
    nlinarith [lowerChord_le_coordinate_square d.thetaB (θ i)]
  obtain ⟨hm,hp⟩ := constructed_lower_core_plateau d.a_pos hη hηsmall hα hcore.le
  have hb := hBound N eps τ lam _ θ i hN he heR.le hτ hτlt hl0 hl1
    (fun x => thresholdStep_range _ _ _) hp hm (hu.le.trans (min_le_left _ _))
  have heq : θ i+d.thetaB-2*Real.pi=θ i-(2*Real.pi-d.thetaB) := by ring
  rw [heq] at hb
  exact hb.trans (by unfold mixedSpectatorMajorant; linarith)

end
end IsingBulk.Tail
