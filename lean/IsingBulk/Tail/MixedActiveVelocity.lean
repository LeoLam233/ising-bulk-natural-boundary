import IsingBulk.Tail.MixedCurrentResidualCoreJets
import IsingBulk.Tail.MixedHybridDensity
import IsingBulk.Analysis.JetsBoundCalculus

/-! Analytic angular velocities on the fixed-spectator active chart.
These are the coefficients multiplying real cutoff derivatives. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

def mixedActiveAngularVelocity {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (i : Fin N) (u : MixedActiveSpace N) : ℂ :=
  (if i∈J then mixedActiveBranch regularA s φ i u else 0)-
    (if i=j then mixedActiveBranch mixedInverseSlope s φ j u*
      ((N:ℂ)*mixedResidualCore (mixedActiveResidualData J j q s φ y u)) else 0)+
    (if i=q then (N:ℂ)*mixedCompactCore (mixedActiveResidualData J j q s φ y u) else 0)

theorem mixedActiveResidualData_zero_actual {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hj : j∈J) (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedActiveResidualData J j q s
      (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ) 0 =
    ((mixedSourceSlope s (deformedPoint f r τ lam θ j))⁻¹,
     mixedSourceSlope s (deformedPoint f r τ lam θ q),
     (∑ i∈J,mixedSourceA s (deformedPoint f r τ lam θ i))/(N:ℂ),
     (∑ i∈Finset.univ.filter (fun i => i∉J),mixedSourceTau s (deformedPoint f r τ lam θ i))/(N:ℂ)) := by
  simp only [mixedActiveResidualData,mixedActiveBranch,mixedActiveCompact,map_zero,
    rotatingCompactCoefficient_formula,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,ite_self,
    add_zero,mul_zero,Complex.exp_zero,mul_one]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact mixed_actual_inverseSlope f hr τ lam s θ j (hsin j hj)
  · exact mixedRootSlope_eq_source (hW q)
  · change (∑ i∈J,regularA s (mixedSourcePhase s (deformedPoint f r τ lam θ i)))/(N:ℂ)=
      (∑ i∈J,mixedSourceA s (deformedPoint f r τ lam θ i))/(N:ℂ)
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact mixed_actual_regularA f hr τ lam s θ i (hsin i hi)
  · change (∑ i∈Finset.univ.filter (fun i => i∉J),mixedRootTau s (deformedPoint f r τ lam θ i))/(N:ℂ)=
      (∑ i∈Finset.univ.filter (fun i => i∉J),mixedSourceTau s (deformedPoint f r τ lam θ i))/(N:ℂ)
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mixedRootTau_eq_source (hW i)

/-- Uniform active angular-velocity jets from the source regular scalar
and residual jets. The only dimension factor is linear. -/
theorem mixedActiveAngularVelocity_jet_bound {N : ℕ} (hN : 1≤N)
    (J : Finset (Fin N)) (j q i : Fin N) (s : ℂ) (φ y : Fin N → ℂ)
    (order : ℕ) (C : ℝ) (hC : 0≤C)
    (hA : ∀ k∈J,JetBound (mixedActiveBranch regularA s φ k) 0 order C)
    (hβ : JetBound (mixedActiveBranch mixedInverseSlope s φ j) 0 order C)
    (hR : JetBound (mixedResidualCore ∘ mixedActiveResidualData J j q s φ y) 0 order C)
    (hQ : JetBound (mixedCompactCore ∘ mixedActiveResidualData J j q s φ y) 0 order C) :
    JetBound (mixedActiveAngularVelocity J j q s φ y i) 0 order
      ((N:ℝ)*(2*C+2^order*C^2)) := by
  have hR' : JetBound (fun u => (N:ℂ)*mixedResidualCore (mixedActiveResidualData J j q s φ y u)) 0 order ((N:ℝ)*C) := by
    refine ⟨analyticAt_const.mul hR.analytic,by positivity,?_⟩
    intro k hk
    exact actual_residual_dimension_scale _ _ hR.analytic N k (hR.bound k hk)
  have hQ' : JetBound (fun u => (N:ℂ)*mixedCompactCore (mixedActiveResidualData J j q s φ y u)) 0 order ((N:ℝ)*C) := by
    refine ⟨analyticAt_const.mul hQ.analytic,by positivity,?_⟩
    intro k hk
    exact actual_residual_dimension_scale _ _ hQ.analytic N k (hQ.bound k hk)
  have hAi : JetBound (fun u => if i∈J then mixedActiveBranch regularA s φ i u else 0) 0 order C := by
    by_cases hi : i∈J
    · simpa only [hi,ite_true] using hA i hi
    · simpa only [hi,ite_false] using (JetBound.const (0:ℂ) (0:MixedActiveSpace N) order).mono le_rfl (by simpa using hC)
  have hh := (hAi.sub ((hβ.mul hR').ite (i=j))).add (hQ'.ite (i=q))
  apply hh.mono le_rfl
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hh := mul_le_mul_of_nonneg_right hn hC
  nlinarith

theorem mixedVelocity_normalized_formula {N : ℕ} (hN : 0<N) (J : Finset (Fin N))
    (a : Fin N → ℂ) (j q i : Fin N) (bj bq D : ℂ) (hb : bj≠0) (hgap : bj-bq≠0) :
    mixedVelocity J a j q ((D+bq*(∑ k∈J,a k))/(bj-bq)) i =
    (if i∈J then a i else 0)-
      (if i=j then bj⁻¹*((N:ℂ)*mixedResidualCore (bj⁻¹,bq,(∑ k∈J,a k)/(N:ℂ),D/(N:ℂ))) else 0)+
      (if i=q then (N:ℂ)*mixedCompactCore (bj⁻¹,bq,(∑ k∈J,a k)/(N:ℂ),D/(N:ℂ)) else 0) := by
  have hn : (N:ℂ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hd : 1-bq*bj⁻¹≠0 := by
    intro he
    have hh := congrArg (fun z : ℂ => z*bj) he
    simp only [sub_mul,one_mul,mul_assoc,inv_mul_cancel₀ hb,mul_one,zero_mul] at hh
    exact hgap hh
  unfold mixedVelocity mixedCompactCore mixedResidualCore
  split_ifs <;> (try field_simp [hn,hb,hgap,hd]) <;> ring

theorem mixedActiveAngularVelocity_zero_source {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q i : Fin N) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hj : j∈J)
    (hsin : ∀ k∈J,Real.sin (θ k)<0)
    (hW : ∀ k,0<(sourceW s (deformedPoint f r τ lam θ k)).im)
    (hb : mixedSourceSlope s (deformedPoint f r τ lam θ j)≠0)
    (hgap : mixedSourceSlope s (deformedPoint f r τ lam θ j)-
      mixedSourceSlope s (deformedPoint f r τ lam θ q)≠0) :
    mixedActiveAngularVelocity J j q s
      (fun k => mixedSourcePhase s (deformedPoint f r τ lam θ k))
      (deformedPoint f r τ lam θ) i 0=mixedContourVelocity J j q f r τ lam s θ i := by
  unfold mixedActiveAngularVelocity
  rw [mixedActiveResidualData_zero_actual J j q f hr τ lam s θ hj hsin hW]
  simp only [mixedActiveBranch,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,add_zero]
  have ha : (if i∈J then regularA s (mixedSourcePhase s (deformedPoint f r τ lam θ i)) else 0)=
      if i∈J then mixedSourceA s (deformedPoint f r τ lam θ i) else 0 := by
    split_ifs with hi
    · exact mixed_actual_regularA f hr τ lam s θ i (hsin i hi)
    · rfl
  have hβ : mixedInverseSlope s (mixedSourcePhase s (deformedPoint f r τ lam θ j))=
      (mixedSourceSlope s (deformedPoint f r τ lam θ j))⁻¹ :=
    mixed_actual_inverseSlope f hr τ lam s θ j (hsin j hj)
  rw [ha,hβ]
  exact (mixedVelocity_normalized_formula hN J (fun k => mixedSourceA s (deformedPoint f r τ lam θ k))
    j q i _ _ _ hb hgap).symm

/-- Uniform jets for a fixed analytic regular branch coefficient, with a
source-derived branch width before particle number and occupancy. -/
theorem mixed_actual_branch_function_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (F : ℂ → ℂ → ℂ)
    (hF : AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) (radialParameter d.theta 0,0))
    (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ c e t₀ C : ℝ,0< inner₀ ∧ inner₀≤cap ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      |sectorDisplacement d.thetaB (θ i)|≤ inner₀ →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      JetBound (mixedActiveBranch F s φ i) 0 order C := by
  obtain ⟨C,hC,hjets⟩ := finite_analytic_jets_bounded _ _ hF order
  have he : ∀ᶠ p in 𝓝 (radialParameter d.theta 0,(0:ℂ)),
      AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) p := hF.eventually_analyticAt
  obtain ⟨U,hU,hOpen,hBase⟩ := eventually_nhds_iff.mp (he.and hjets)
  obtain ⟨inner₀,c,e,t₀,hi,hicap,hc,heps,ht,hBranch⟩ :=
    mixed_actual_branch_chart_neighborhood d hcsmall U hOpen hBase cap hcap
  refine ⟨inner₀,c,e,t₀,C,hi,hicap,hc,heps,ht,hC,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ i s hN heps0 hepslt hτ hl0 hl1 htl hprofile hs
  have hb := hBranch η α hη hηsmall hα N eps τ lam θ i s hN heps0 hepslt hτ hl0 hl1 htl hprofile hs
  have hh := hU _ hb
  refine ⟨(mixedActiveBranch_jet_bound F s _ i 0 hh.1).1,hC.le,?_⟩
  intro k hk
  exact ((mixedActiveBranch_jet_bound F s _ i k hh.1).2).trans (hh.2 k hk)

theorem mixedBranchResidual_zero_source {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hj : j∈J) (hq : q∉J)
    (hsin : ∀ k∈J,Real.sin (θ k)<0)
    (hW : ∀ k,0<(sourceW s (deformedPoint f r τ lam θ k)).im)
    (hg : deformedPoint f r τ lam θ j-(deformedPoint f r τ lam θ j)⁻¹≠0)
    (hb : mixedSourceSlope s (deformedPoint f r τ lam θ j)≠0)
    (hgap : mixedSourceSlope s (deformedPoint f r τ lam θ j)-mixedSourceSlope s (deformedPoint f r τ lam θ q)≠0) :
    mixedBranchResidual J j q f r τ lam s θ j=(N:ℂ)*mixedResidualCore
      (mixedActiveResidualData J j q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ) 0) := by
  have hjq : j≠q := by intro h; subst q; exact hq hj
  have hv := mixedActiveAngularVelocity_zero_source hN J j q j f hr τ lam s θ hj hsin hW hb hgap
  unfold mixedBranchResidual
  rw [← hv]
  simp only [mixedActiveAngularVelocity,hj,hjq,ite_true,ite_false,add_zero,
    mixedActiveBranch,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,add_zero]
  have ha : regularA s (mixedSourcePhase s (deformedPoint f r τ lam θ j))=
      mixedSourceA s (deformedPoint f r τ lam θ j) := mixed_actual_regularA f hr τ lam s θ j (hsin j hj)
  have hβ : mixedInverseSlope s (mixedSourcePhase s (deformedPoint f r τ lam θ j))=
      (mixedSourceSlope s (deformedPoint f r τ lam θ j))⁻¹ := mixed_actual_inverseSlope f hr τ lam s θ j (hsin j hj)
  rw [ha,hβ,mul_sub,mixedSourceSlope_mul_A hg]
  simp only [← mul_assoc,mul_inv_cancel₀ hb,one_mul]
  ring

theorem mixedCompactVelocity_zero_source {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (hj : j∈J) (hq : q∉J)
    (hsin : ∀ k∈J,Real.sin (θ k)<0)
    (hW : ∀ k,0<(sourceW s (deformedPoint f r τ lam θ k)).im)
    (hb : mixedSourceSlope s (deformedPoint f r τ lam θ j)≠0)
    (hgap : mixedSourceSlope s (deformedPoint f r τ lam θ j)-mixedSourceSlope s (deformedPoint f r τ lam θ q)≠0) :
    mixedContourVelocity J j q f r τ lam s θ q=(N:ℂ)*mixedCompactCore
      (mixedActiveResidualData J j q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ) 0) := by
  have hqj : q≠j := by intro h; subst q; exact hq hj
  have hv := mixedActiveAngularVelocity_zero_source hN J j q q f hr τ lam s θ hj hsin hW hb hgap
  simpa only [mixedActiveAngularVelocity,hq,hqj,ite_false,ite_true,sub_zero,zero_add] using hv.symm

end
end IsingBulk.Tail
