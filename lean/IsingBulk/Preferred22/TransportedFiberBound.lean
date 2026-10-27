import IsingBulk.Preferred22.JacobianResolvent
import IsingBulk.Preferred22.ShiftedBoxIntegration

/-! Genuine physical fiber integration for the actual transported density.
The one explicit pointwise hypothesis is the remaining q20 scalar/minor
majorant; no integrated shell bound or complete-tail bound is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory

set_option maxHeartbeats 1400000 in
/-- Actual transported-density fiber domination from its explicit q20
pointwise majorant. Arbitrary relabelings are permitted without assuming
symmetry of the transported density. The original occupancies, both extreme
Jacobian factors and the entire physical product denominator are retained. -/
theorem preferred_q20_fiber_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n : ℕ, ∀ ε τ c r δB K : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → 0 ≤ K → ∀ f : (Fin (n+2) → ℝ) → ℝ,
      ∀ e : Equiv.Perm (Fin (n+2)), ∀ z : Fin n → ℝ,
      (∀ m ∈ extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        f (preferredFiberConfiguration c z m ∘ e) ≤
        K*preferredJacobianResolvent d B ε τ (preferredFiberConfiguration c z m ∘ e)) →
      (∫⁻ m in extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        ENNReal.ofReal (f (preferredFiberConfiguration c z m ∘ e))) ≤
      (preferredShiftedOneBodyBox n d.b (d.b+c/((n+2:ℕ):ℝ)) r).indicator
        (fun z => ENNReal.ofReal (K*A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*
          (C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|)))) z := by
  obtain ⟨A,εa,τa,δa,hA,hεa,hτa,hδa,hδaδ,ha⟩ := preferred_geometric_fiber_jacobian_bound d B
  obtain ⟨C,εc,τc,δc,hC,hεc,hτc,hδc,_,hc⟩ := preferred_geometric_fiber_pair_lintegral d B
  let δ₀ := min δa δc
  refine ⟨A,C,min εa εc,min τa τc,δ₀,hA,hC,lt_min hεa hεc,lt_min hτa hτc,
    lt_min hδa hδc,(min_le_left _ _).trans_lt hδaδ,?_⟩
  intro n ε τ c r δB K hε hεr hτ hτr hr _hδB hδ hK f e z hpoint
  let F := extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z
  let W := preferredShiftedOneBodyBox n d.b (d.b+c/((n+2:ℕ):ℝ)) r
  by_cases hz : z ∈ W
  · rw [Set.indicator_of_mem hz]
    have hδa' : δB ≤ δa := hδ.trans (min_le_left _ _)
    have hδc' : δB ≤ δc := hδ.trans (min_le_right _ _)
    let L := K*A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))
    have hL : 0 ≤ L := by dsimp [L,preferredOneBodyMajorant]; positivity
    let pair := fun m : ℝ =>
      preferredExtremePair d B ε τ (preferredFiberConfiguration c z m) 0 (Fin.last (n+1)) /
        ‖1-preferredActualZ d B ε τ (preferredFiberConfiguration c z m)‖
    have hpt (m : ℝ) (hm : m ∈ F) :
        ENNReal.ofReal (f (preferredFiberConfiguration c z m ∘ e)) ≤
          ENNReal.ofReal L * ENNReal.ofReal (pair m) := by
      have hp := hpoint m hm
      rw [preferredJacobianResolvent_equiv] at hp
      have hj := ha n ε τ c r δB hε (hεr.trans_le (min_le_left _ _)) hτ
        (hτr.trans_le (min_le_left _ _)) hδa' z m hm
      have hreal : f (preferredFiberConfiguration c z m ∘ e) ≤ L*pair m := by
        calc
          _ ≤ K*preferredJacobianResolvent d B ε τ (preferredFiberConfiguration c z m) := hp
          _ ≤ K*(A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*pair m) :=
            mul_le_mul_of_nonneg_left hj hK
          _ = _ := by dsimp [L]; ring
      rw [← ENNReal.ofReal_mul hL]
      exact ENNReal.ofReal_le_ofReal hreal
    have hmono : (∫⁻ m in F, ENNReal.ofReal (f (preferredFiberConfiguration c z m ∘ e))) ≤
        ∫⁻ m in F, ENNReal.ofReal L * ENNReal.ofReal (pair m) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (extremeShellFiber_isClosed _ _ _ _ _).measurableSet] with m hm
      exact hpt m hm
    have hsub : F ⊆ extremeShellFiber (c-∑ i,z i) r (-d.b-δc) B.delta z := by
      intro m hm
      exact ⟨by linarith [hm.1],hm.2⟩
    have hpair : (∫⁻ m in F, ENNReal.ofReal (pair m)) ≤
        ENNReal.ofReal (C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|)) :=
      (lintegral_mono_set hsub).trans (hc n ε τ c r hε
        (hεr.trans_le (min_le_right _ _)) hτ (hτr.trans_le (min_le_right _ _)) hr z)
    calc
      _ ≤ ∫⁻ m in F, ENNReal.ofReal L * ENNReal.ofReal (pair m) := hmono
      _ = ENNReal.ofReal L * ∫⁻ m in F, ENNReal.ofReal (pair m) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal
          (C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|)) :=
        by simpa only [mul_comm] using mul_le_mul_left hpair (ENNReal.ofReal L)
      _ = _ := by rw [← ENNReal.ofReal_mul hL]
  · have hF : F=∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro m hm
      apply hz
      apply preferredShiftedOneBodyBox_mem.mpr
      intro i
      have hw := preferredFiberConfiguration_mean_window d hm i.succ.castSucc
      simpa only [preferredFiberConfiguration_other] using hw
    change (∫⁻ m in F, _) ≤ _
    rw [hF,setLIntegral_empty,Set.indicator_of_notMem hz]


/-- Literal transported-density specialization of the genuine q20 fiber integral. -/
theorem preferred_transported_density_fiber_lintegral (d : PreferredBranchData)
    (B : PreferredCoareaBump d) :
    ∃ A C ε₀ τ₀ δ₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧ 0 < δ₀ ∧ δ₀ < B.delta ∧
      ∀ n j : ℕ, ∀ ε τ c r δB K : ℝ, 0 < ε → ε < ε₀ → 0 ≤ τ → τ < τ₀ →
      0 < r → 0 < δB → δB ≤ δ₀ → 0 ≤ K → ∀ η rcut : ℝ → ℝ,
      ∀ e : Equiv.Perm (Fin (n+2)), ∀ z : Fin n → ℝ,
      (∀ m ∈ extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        ‖preferredTransportedDensity .right τ η B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredFiberConfiguration c z m ∘ e)‖ ≤
        K*preferredJacobianResolvent d B ε τ (preferredFiberConfiguration c z m ∘ e)) →
      (∫⁻ m in extremeShellFiber (c-∑ i,z i) r (-d.b-δB) B.delta z,
        ENNReal.ofReal ‖preferredTransportedDensity .right τ η B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε) (preferredFiberConfiguration c z m ∘ e)‖) ≤
      (preferredShiftedOneBodyBox n d.b (d.b+c/((n+2:ℕ):ℝ)) r).indicator
        (fun z => ENNReal.ofReal (K*A^n*(∏ i,preferredOneBodyMajorant ε (z i+d.b))*
          (C*((n+2:ℕ):ℝ)*Real.sqrt (|d.b+c/((n+2:ℕ):ℝ)|+r+ε)/r*(1+|Real.log ε|)))) z := by
  obtain ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hb⟩ := preferred_q20_fiber_lintegral d B
  refine ⟨A,C,ε₀,τ₀,δ₀,hA,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro n j ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK η rcut e z hpoint
  exact hb n ε τ c r δB K hε hεr hτ hτr hr hδB hδ hK
    (fun θ => ‖preferredTransportedDensity .right τ η B.p B.m rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε) θ‖) e z hpoint

end
end IsingBulk.Preferred22
