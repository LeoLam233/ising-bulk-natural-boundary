import IsingBulk.Tail.MixedPositiveSourceGeometry

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def mixedPositiveKernelMajorant {N : ℕ} (d : LocalBranchData) (η α B eps τ lam : ℝ)
    (j q : Fin N) (θ : Fin N → ℝ) : ℝ :=
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*‖mixedSimpleKernel f r τ lam s θ‖*
    ∏ i∈(Finset.univ.erase j).erase q,mixedSpectatorMajorant d.thetaB B eps (θ i)

def mixedPositiveIntegralBudget (N : ℕ) (a b C : ℝ) : ℝ :=
  (48/5:ℝ)*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
    ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2))

/-- Absolute integration on actual source positive cells. At lambda zero
selector independence removes the upper-plateau condition on the anchor.
At nonzero lambda the proved open upper plateau is retained. -/
theorem mixed_positive_source_cell_integral (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (η α outer B : ℝ)
    (hη : 0<η) (hηsmall : η≤Real.sin d.thetaB/4) (hα : 0<α) (ho : 0<outer) (hB : 0≤B) :
    ∃ R t₀ : ℝ,0<R ∧ 0<t₀ ∧ ∀ τ : ℝ,0≤τ → τ<t₀ →
      ∃ a e : ℝ,0<a ∧ 0<e ∧ ∀ (N : ℕ) (j q : Fin N) (I : ℝ×ℝ),j≠q →
      (∀ x∈Icc I.1 I.2,outer/2≤|sectorDisplacement d.thetaB x|) →
      ∀ eps lam : ℝ,0<eps → eps<e → 0≤lam → lam≤1 →
      (lam=0 ∨ ∀ x∈Icc I.1 I.2,3*α/4<Real.sin x) →
      let S := mixedAngularCell j q (2*Real.pi-d.thetaB,2*Real.pi-d.thetaB+R) I
      IntegrableOn (mixedPositiveKernelMajorant d η α B eps τ lam j q) S ∧
      (∫ θ in S,mixedPositiveKernelMajorant d η α B eps τ lam j q θ)≤
        mixedPositiveIntegralBudget N (d.c₀*eps) (a*eps)
          (2*Real.pi+4*B*Real.sqrt (2*Real.pi)) := by
  obtain ⟨R,eG,t₀,hR,heG,ht,hRη,hGeometry⟩ := mixed_positive_source_geometry d hcsmall η α outer
    hη hηsmall hα ho
  refine ⟨R,t₀,hR,ht,?_⟩
  intro τ hτ hτlt
  let f := constructedSelector d.thetaB η α
  have hf := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  obtain ⟨cF,eF,a,hcF,_hcF1,heF,_heF1,ha,hFloors⟩ := mixed_actual_product_floors d.theta d.c₀ τ
    (Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos]))
    d.c₀_pos hcsmall hτ f hf.p_nonneg (fun _ => (thresholdStep_range _ _ _).2)
    hf.m_nonneg (fun _ => Real.smoothTransition.le_one _) hf.p_zero hf.m_zero
  let e := min eG (min eF (min (1/(d.c₀+1)) (1/(a+1))))
  have he : 0<e := by dsimp [e]; positivity [d.c₀_pos]
  refine ⟨a,e,ha,he,?_⟩
  intro N j q I hjq hgap eps lam heps hepslt hl0 hl1 hplateau
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let L := mixedSpectatorMajorant d.thetaB B eps
  let C := 2*Real.pi+4*B*Real.sqrt (2*Real.pi)
  let S := mixedAngularCell j q (2*Real.pi-d.thetaB,2*Real.pi-d.thetaB+R) I
  have hN : 1≤N := by have := j.isLt; omega
  have hgeo (θ : Fin N → ℝ) (hθ : θ∈S) := hGeometry N eps τ lam θ j q hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hτlt hl0 hl1
    (by have hh := hθ.1.2.1; dsimp at hh; linarith)
    (by have hh := hθ.1.2.2; dsimp at hh; linarith) (hgap (θ q) hθ.2)
  have hfloor (θ : Fin N → ℝ) := hFloors N hN eps lam heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hl0 hl1 θ s (by dsimp [s]; simp; positivity)
  have haY : 0<d.c₀*eps := mul_pos d.c₀_pos heps
  have haZ : 0<a*eps := mul_pos ha heps
  have haY1 : d.c₀*eps≤1 := by
    have hh := hepslt.le.trans ((min_le_right eG _).trans ((min_le_right eF _).trans (min_le_left _ _)))
    have hh' := (le_div_iff₀ (show 0<d.c₀+1 by linarith [d.c₀_pos])).mp hh
    nlinarith
  have haZ1 : a*eps≤1 := by
    have hh := hepslt.le.trans ((min_le_right eG _).trans ((min_le_right eF _).trans (min_le_right _ _)))
    have hh' := (le_div_iff₀ (show 0<a+1 by linarith)).mp hh
    nlinarith
  have hL0 (t : ℝ) : 0≤L t := zero_le_one.trans (mixedSpectatorMajorant_one_le d.thetaB hB t)
  have hLc : ContinuousOn L (Icc 0 (2*Real.pi)) := (mixedSpectatorMajorant_continuous _ _ heps).continuousOn
  have hLint : (∫ t in Icc 0 (2*Real.pi),L t)≤C :=
    (mixedSpectatorMajorant_integral d.thetaB_pos.le (by linarith [d.thetaB_lt,Real.pi_pos]) hB heps).2
  have hbox : S⊆angleBox N := fun _ hθ => hθ.1.1
  rcases hplateau with hzero | hupper
  · subst lam
    have h0geo (θ : Fin N → ℝ) (hθ : θ∈S) := hgeo θ hθ
    simp only [deformedPoint_zero] at h0geo
    have hh := mixed_positive_global_kernel_integral mixedZeroSelector (Real.exp_pos _) τ 0 s j q hjq
      (mixedAngularCell_measurable _ _ _ _) (mixedAngularCell_convex _ _ _ _)
      contDiff_const contDiff_const hbox
      (fun _ _ _ _ => ⟨deriv_const _ _,deriv_const _ _⟩)
      (by simpa only [deformedPoint_zero] using fun θ hθ => (h0geo θ hθ).1)
      (by simpa only [deformedPoint_zero] using fun θ hθ => (h0geo θ hθ).2.1)
      (by simpa only [deformedPoint_zero] using fun θ hθ => (h0geo θ hθ).2.2.1)
      (by simpa only [deformedPoint_zero] using fun θ hθ => (h0geo θ hθ).2.2.2)
      L C hL0 hLc hLint haY haY1 haZ haZ1
      (by simpa only [deformedPoint_zero,neg_mul] using fun θ (_ : θ∈S) => (hfloor θ).1)
      (by simpa only [deformedPoint_zero,neg_mul] using fun θ (_ : θ∈S) => (hfloor θ).2)
    unfold mixedPositiveKernelMajorant mixedPositiveIntegralBudget
    simpa only [mixedSimpleKernel,deformedPoint_zero] using hh
  · have hpq (θ : Fin N → ℝ) (hθ : θ∈S) (k : Fin N) (hk : k=j ∨ k=q) :
        deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0 := by
      rcases hk with hk | hk
      · rw [hk]
        have hu : |θ j+d.thetaB-2*Real.pi|≤R := by
          have hlo := hθ.1.2.1
          have hhi := hθ.1.2.2
          dsimp at hlo hhi
          exact abs_le.mpr ⟨by linarith,by linarith⟩
        obtain ⟨hp,hm⟩ := mixed_lower_angular_plateau d.a_pos hη hηsmall hα hR.le hRη hu
        exact ⟨hp.deriv_eq.trans (deriv_const _ _),hm.deriv_eq.trans (deriv_const _ _)⟩
      · rw [hk]
        obtain ⟨hp,hm⟩ := mixed_upper_open_plateau_germ d.a_pos hη hηsmall hα (hupper (θ q) hθ.2)
        exact ⟨hp.deriv_eq.trans (deriv_const _ _),hm.deriv_eq.trans (deriv_const _ _)⟩
    exact mixed_positive_global_kernel_integral f (Real.exp_pos _) τ lam s j q hjq
      (mixedAngularCell_measurable _ _ _ _) (mixedAngularCell_convex _ _ _ _) hf.p_smooth hf.m_smooth hbox
      hpq (fun θ hθ => (hgeo θ hθ).1) (fun θ hθ => (hgeo θ hθ).2.1)
      (fun θ hθ => (hgeo θ hθ).2.2.1) (fun θ hθ => (hgeo θ hθ).2.2.2)
      L C hL0 hLc hLint haY haY1 haZ haZ1
      (fun θ _ => by simpa only [neg_mul] using (hfloor θ).1)
      (fun θ _ => by simpa only [neg_mul] using (hfloor θ).2)

end
end IsingBulk.Tail
