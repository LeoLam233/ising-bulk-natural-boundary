import IsingBulk.Tail.CompactPhaseSourceJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

lemma jet_comp_contraction_right {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : E →L[ℝ] F) (hgn : ‖g‖≤1) (f : F→G) (hf : ContDiff ℝ ∞ f) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ k f (g x)‖ := by
  rw [g.iteratedFDeriv_comp_right hf x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hgn)

def currentPhaseJointPoint {N : ℕ} (f : SelectorFunctions) (c eps tau lam : ℝ)
    (i : Fin N) (p : ℂ × (Fin N→ℝ)) : ℂ × ℂ × ℂ :=
  (p.1,(currentPhaseAngularPoint f c eps tau lam 0 i p.2).2)

lemma currentPhaseJointPoint_smooth {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c eps tau lam : ℝ) (i : Fin N) : ContDiff ℝ ∞ (currentPhaseJointPoint f c eps tau lam i) :=
  contDiff_fst.prodMk (((currentPhaseAngularPoint_smooth f hp hm c eps tau lam 0 i).comp contDiff_snd).snd)

lemma currentPhaseJointPoint_positive_jet {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c eps tau lam : ℝ) (i : Fin N) (p : ℂ × (Fin N→ℝ))
    (ht : 0≤tau) (ht1 : tau≤1) (hl : 0≤lam) (hl1 : lam≤1)
    (C : ℝ) (hC : 0≤C) (k : ℕ) (hk : 1≤k)
    (hb : ‖iteratedFDeriv ℝ k (normalizedRetractionShift N f.p f.m i) p.2‖≤C) :
    ‖iteratedFDeriv ℝ k (currentPhaseJointPoint f c eps tau lam i) p‖≤1+C := by
  let A := currentPhaseAngularPoint f c eps tau lam 0 i
  let L : (ℂ × (Fin N→ℝ)) →L[ℝ] (Fin N→ℝ) := ContinuousLinearMap.snd ℝ ℂ (Fin N→ℝ)
  let R : (ℂ × ℂ × ℂ) →L[ℝ] (ℂ × ℂ) := ContinuousLinearMap.snd ℝ ℂ (ℂ × ℂ)
  let S : (ℂ × (Fin N→ℝ)) →L[ℝ] ℂ := ContinuousLinearMap.fst ℝ ℂ (Fin N→ℝ)
  have hL : ‖L‖≤1 := L.opNorm_le_bound zero_le_one (fun x => by simpa [L] using norm_snd_le x)
  have hR : ‖R‖≤1 := R.opNorm_le_bound zero_le_one (fun x => by simpa [R] using norm_snd_le x)
  have hS : ‖S‖≤1 := S.opNorm_le_bound zero_le_one (fun x => by simpa [S] using norm_fst_le x)
  have hAs : ContDiff ℝ ∞ A := currentPhaseAngularPoint_smooth f hp hm c eps tau lam 0 i
  have hAL : ContDiff ℝ ∞ (A ∘ L) := hAs.comp L.contDiff
  have hALb : ‖iteratedFDeriv ℝ k (A ∘ L) p‖≤1+C :=
    (jet_comp_contraction_right L hL A hAs p k).trans
      (currentPhaseAngularPoint_positive_jet f hp hm c eps tau lam 0 i p.2 ht ht1 hl hl1 C hC k hk hb)
  have hRb := R.norm_iteratedFDeriv_comp_left (x := p) hAL.contDiffAt (by simp : (k:ℕ∞ω)≤∞)
  have hbound : ‖iteratedFDeriv ℝ k (R ∘ A ∘ L) p‖≤1+C :=
    (hRb.trans (mul_le_of_le_one_left (norm_nonneg _) hR)).trans hALb
  change ‖iteratedFDeriv ℝ k (fun x => (S x,(R ∘ A ∘ L) x)) p‖≤1+C
  rw [iteratedFDeriv_prodMk S.contDiff.contDiffAt (R.contDiff.comp hAL).contDiffAt (by simp : (k:ℕ∞ω)≤∞)]
  exact (multilinear_prod_norm_le_max _ _).trans (max_le
    ((positive_linear_jet_bound S hS p k hk).trans (by linarith)) hbound)

lemma real_source_model_composition_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ × ℂ × ℂ) (hg : ContDiff ℝ ∞ g) (x : E)
    (ha : AnalyticAt ℂ compactPhaseSourceModel (g x)) (k : ℕ) (B D : ℝ)
    (hB : ∀ i ≤ k, ‖iteratedFDeriv ℝ i compactPhaseSourceModel (g x)‖≤B)
    (hD : ∀ (i : ℕ), 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i g x‖≤D^i) :
    ‖iteratedFDeriv ℝ k (compactPhaseSourceModel ∘ g) x‖≤k.factorial*B*D^k := by
  let V := {p : ℂ × ℂ × ℂ | AnalyticAt ℂ compactPhaseSourceModel p}
  have hv : IsOpen V := isOpen_analyticAt ℂ compactPhaseSourceModel
  have hx : g x ∈ V := ha
  have hu : IsOpen (g ⁻¹' V) := hv.preimage hg.continuous
  have hfa : ContDiffOn ℝ ∞ compactPhaseSourceModel V := fun p hp =>
    ((hp.contDiffAt : ContDiffAt ℂ ∞ compactPhaseSourceModel p).restrict_scalars ℝ).contDiffWithinAt
  have hh := norm_iteratedFDerivWithin_comp_le hfa (hg.contDiffOn (s := g ⁻¹' V))
    (n := k) (by simp) hv.uniqueDiffOn hu.uniqueDiffOn (fun _ hy => hy) hx
    (C := B) (D := D) (by simpa only [iteratedFDerivWithin_of_isOpen _ hv hx] using hB)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hu hx] using hD)
  simpa only [iteratedFDerivWithin_of_isOpen _ hu hx] using hh

/-- True joint source-parameter/angular finite jets of the fully coupled phase.
The contour radius stays fixed during differentiation. -/
theorem actual_compact_phase_joint_jets (d : LocalBranchData) (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi))
    (hpv : ∀ x, 0≤f.p x ∧ f.p x≤1) (hmv : ∀ x, 0≤f.m x ∧ f.m x≤1)
    {a b : ℝ} (hmargin : ∀ theta ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos theta|<1)
    (J : ℕ) : ∃ r C : ℝ, 0<r ∧ 0<C ∧
      ∀ N : ℕ, 0<N → ∀ eps tau lam : ℝ, 0≤eps → 0≤tau → tau≤1 → 0≤lam → lam≤1 →
      ∀ s : ℂ, ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam≤r →
      ∀ theta : Fin N → ℝ, (∀ i, theta i ∈ Icc a b) → ∀ k≤J,
      ‖iteratedFDeriv ℝ k (fun p : ℂ × (Fin N→ℝ) =>
        currentComplexPhase f (Real.exp (-d.c₀*eps)) tau lam p.1 p.2) (s,theta)‖ ≤ C*N := by
  obtain ⟨r,B,hr,hB,hmodel⟩ := compactPhaseSourceModel_compact_tube d hmargin J
  obtain ⟨A,hA,hret⟩ := periodic_retraction_finite_jets f hp hm hpper hmper J
  let C := (J.factorial:ℝ)*B*(1+A)^J
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨r,C,hr,hC,?_⟩
  intro N hN eps tau lam he ht ht1 hl hl1 s hsmall theta htheta k hk
  let g : Fin N → (ℂ × (Fin N → ℝ)) → ℂ × ℂ × ℂ :=
    fun i => currentPhaseJointPoint f d.c₀ eps tau lam i
  have hgs (i : Fin N) : ContDiff ℝ ∞ (g i) :=
    currentPhaseJointPoint_smooth f hp hm d.c₀ eps tau lam i
  have hpoints (i : Fin N) : AnalyticAt ℂ compactPhaseSourceModel (g i (s,theta)) ∧
      ∀ j≤J, ‖iteratedFDeriv ℝ j compactPhaseSourceModel (g i (s,theta))‖≤B := by
    let v := -d.c₀*eps+lam*tau*normalizedRetractionShift N f.p f.m i theta
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have hP0 := occupancy_nonneg (fun l => (hpv (theta l)).1)
    have hP1 := occupancy_le (fun l => (hpv (theta l)).2)
    have hv : |v|≤d.c₀*eps+2*tau*lam := by
      simpa only [v,normalizedRetractionShift,normalizedAngularOccupancy,occupancy,coupledRadialExponent] using
        coupledRadialExponent_lambda_bound d.c₀_pos.le he ht hl
          (hpv (theta i)).1 (hpv (theta i)).2 (hmv (theta i)).1 (hmv (theta i)).2
          (div_nonneg hP0 hn.le) ((div_le_one hn).mpr hP1)
    apply hmodel (theta i) (htheta i) s (v:ℂ)
    rw [max_le_iff,Complex.norm_real,Real.norm_eq_abs]
    have htl : tau*lam≤lam := mul_le_of_le_one_left hl ht1
    constructor <;> nlinarith [norm_nonneg (s-radialParameter d.theta 0),mul_nonneg d.c₀_pos.le he]
  have hcomp (i : Fin N) : ContDiffAt ℝ ∞ (compactPhaseSourceModel ∘ g i) (s,theta) :=
    (((hpoints i).1.contDiffAt : ContDiffAt ℂ ∞ compactPhaseSourceModel (g i (s,theta))).restrict_scalars ℝ).comp (s,theta) (hgs i).contDiffAt
  have hfb (i : Fin N) : ‖iteratedFDeriv ℝ k (compactPhaseSourceModel ∘ g i) (s,theta)‖≤C := by
    have hh := real_source_model_composition_jet_bound (g i) (hgs i) (s,theta) (hpoints i).1 k B (1+A)
      (fun j hj => (hpoints i).2 j (hj.trans hk)) (by
        intro j hj hjk
        have hb := currentPhaseJointPoint_positive_jet f hp hm d.c₀ eps tau lam i (s,theta)
          ht ht1 hl hl1 A (by linarith) j hj (hret N hN i theta j (hjk.trans hk))
        exact hb.trans (le_self_pow₀ (by linarith : 1≤1+A) (by omega)))
    apply hh.trans
    dsimp [C]
    have hbase : 1≤1+A := by linarith
    gcongr
  have heq : (fun p : ℂ × (Fin N→ℝ) => currentComplexPhase f (Real.exp (-d.c₀*eps)) tau lam p.1 p.2) =
      (fun x => ∑ i, compactPhaseSourceModel (g i x)) := by
    funext x
    unfold currentComplexPhase
    apply Finset.sum_congr rfl
    intro i _
    exact currentPhaseAngularPoint_source f d.c₀ eps tau lam x.1 i x.2
  have hcomp' (i : Fin N) : ContDiffAt ℝ k (fun x => compactPhaseSourceModel (g i x)) (s,theta) :=
    (hcomp i).of_le (by simp)
  rw [heq,iteratedFDeriv_fun_sum_apply (fun i _ => hcomp' i)]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ k (compactPhaseSourceModel ∘ g i) (s,theta)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hfb i)
    _ = C*N := by simp [mul_comm]

end
end IsingBulk.Tail
