import IsingBulk.Tail.CompactFirstJetPerturbation
import IsingBulk.Tail.CompactLogYJets
import IsingBulk.Tail.CompactRightActualCurvature

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

lemma periodic_retraction_finite_jets (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi))
    (J : ℕ) : ∃ C : ℝ, 1≤C ∧ ∀ N : ℕ, 0<N → ∀ i : Fin N, ∀ theta : Fin N → ℝ,
      ∀ k≤J, ‖iteratedFDeriv ℝ k (normalizedRetractionShift N f.p f.m i) theta‖≤C := by
  induction J with
  | zero =>
    obtain ⟨C,hC,hb⟩ := periodic_retraction_jet_bound f.p f.m hp hm hpper hmper 0
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro N hN i theta k hk
    have hk0 : k=0 := by omega
    subst k
    exact (hb N hN i theta).trans (le_max_right _ _)
  | succ J ih =>
    obtain ⟨C,hC,hb⟩ := ih
    obtain ⟨D,hD,hd⟩ := periodic_retraction_jet_bound f.p f.m hp hm hpper hmper (J+1)
    refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
    intro N hN i theta k hk
    by_cases hkJ : k≤J
    · exact (hb N hN i theta k hkJ).trans (le_max_left _ _)
    · have he : k=J+1 := by omega
      subst k
      exact (hd N hN i theta).trans (le_max_right _ _)

lemma multilinear_prod_norm_le_max {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G) :
    ‖A.prod B‖≤max ‖A‖ ‖B‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound ((norm_nonneg A).trans (le_max_left _ _))
  intro m
  change max ‖A m‖ ‖B m‖≤_
  apply max_le
  · exact (A.le_opNorm m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (B.le_opNorm m).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

lemma positive_linear_jet_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (hL : ‖L‖≤1) (x : E) (k : ℕ) (hk : 1≤k) : ‖iteratedFDeriv ℝ k L x‖≤1 := by
  cases k with
  | zero => omega
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L=(fun _ => L) := by funext y; exact L.fderiv
    rw [he]
    cases k with
    | zero => simpa using hL
    | succ k => simp [iteratedFDeriv_succ_const]

lemma real_model_composition_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℂ × ℂ × ℂ) (hg : ContDiff ℝ ∞ g) (x : E)
    (ha : AnalyticAt ℂ compactPhaseModel (g x)) (k : ℕ) (B D : ℝ)
    (hB : ∀ i ≤ k, ‖iteratedFDeriv ℝ i compactPhaseModel (g x)‖≤B)
    (hD : ∀ (i : ℕ), 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i g x‖≤D^i) :
    ‖iteratedFDeriv ℝ k (compactPhaseModel ∘ g) x‖≤k.factorial*B*D^k := by
  let V := {p : ℂ × ℂ × ℂ | AnalyticAt ℂ compactPhaseModel p}
  have hv : IsOpen V := isOpen_analyticAt ℂ compactPhaseModel
  have hx : g x ∈ V := ha
  have hu : IsOpen (g ⁻¹' V) := hv.preimage hg.continuous
  have hfa : ContDiffOn ℝ ∞ compactPhaseModel V := fun p hp =>
    ((hp.contDiffAt : ContDiffAt ℂ ∞ compactPhaseModel p).restrict_scalars ℝ).contDiffWithinAt
  have hh := norm_iteratedFDerivWithin_comp_le hfa (hg.contDiffOn (s := g ⁻¹' V))
    (n := k) (by simp) hv.uniqueDiffOn hu.uniqueDiffOn (fun _ hy => hy) hx
    (C := B) (D := D) (by simpa only [iteratedFDerivWithin_of_isOpen _ hv hx] using hB)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hu hx] using hD)
  simpa only [iteratedFDerivWithin_of_isOpen _ hu hx] using hh

def currentPhaseAngularPoint {N : ℕ} (f : SelectorFunctions) (c0 eps tau lam : ℝ)
    (s : ℂ) (i : Fin N) (theta : Fin N → ℝ) : ℂ × ℂ × ℂ :=
  (sourceS s,((-c0*eps+lam*tau*normalizedRetractionShift N f.p f.m i theta:ℝ):ℂ),(theta i:ℂ))

lemma currentPhaseAngularPoint_smooth {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c0 eps tau lam : ℝ) (s : ℂ) (i : Fin N) :
    ContDiff ℝ ∞ (currentPhaseAngularPoint f c0 eps tau lam s i) := by
  have hv : ContDiff ℝ ∞ (fun x => -c0*eps+lam*tau*normalizedRetractionShift N f.p f.m i x) :=
    contDiff_const.add ((normalizedRetractionShift_smooth N f.p f.m hp hm i).const_smul (lam*tau))
  exact contDiff_const.prodMk ((Complex.ofRealCLM.contDiff.comp hv).prodMk
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)))

lemma currentPhaseAngularPoint_source {N : ℕ} (f : SelectorFunctions)
    (c0 eps tau lam : ℝ) (s : ℂ) (i : Fin N) (theta : Fin N → ℝ) :
    continuedPhase (sourceW s (deformedPoint f (Real.exp (-c0*eps)) tau lam theta i))=
      compactPhaseModel (currentPhaseAngularPoint f c0 eps tau lam s i theta) := by
  simpa only [currentPhaseAngularPoint,coupledRadialExponent,normalizedRetractionShift,
    normalizedAngularOccupancy,occupancy] using compactPhaseModel_source_identity f c0 eps tau lam s theta i

lemma currentPhaseAngularPoint_positive_jet {N : ℕ} (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (c0 eps tau lam : ℝ) (s : ℂ) (i : Fin N) (theta : Fin N → ℝ)
    (ht : 0≤tau) (ht1 : tau≤1) (hl : 0≤lam) (hl1 : lam≤1)
    (C : ℝ) (hC : 0≤C) (k : ℕ) (hk : 1≤k)
    (hb : ‖iteratedFDeriv ℝ k (normalizedRetractionShift N f.p f.m i) theta‖≤C) :
    ‖iteratedFDeriv ℝ k (currentPhaseAngularPoint f c0 eps tau lam s i) theta‖≤1+C := by
  let v : (Fin N → ℝ) → ℝ := fun x => -c0*eps+lam*tau*normalizedRetractionShift N f.p f.m i x
  have hv : ContDiff ℝ ∞ v := contDiff_const.add
    ((normalizedRetractionShift_smooth N f.p f.m hp hm i).const_smul (lam*tau))
  have hvC : ContDiff ℝ ∞ (fun x => (v x:ℂ)) := Complex.ofRealCLM.contDiff.comp hv
  let L : (Fin N → ℝ) →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
  have hLn : ‖L‖≤1 := L.opNorm_le_bound zero_le_one (fun x => by
    simpa only [L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,Complex.ofRealCLM_apply,
      Complex.norm_real,one_mul] using norm_le_pi_norm x i)
  have hangle := positive_linear_jet_bound L hLn theta k hk
  have hvb : ‖iteratedFDeriv ℝ k v theta‖≤C := by
    have hmuli : ContDiff ℝ ∞ (fun x => lam*tau*normalizedRetractionShift N f.p f.m i x) :=
      (normalizedRetractionShift_smooth N f.p f.m hp hm i).const_smul (lam*tau)
    dsimp only [v]
    rw [fun_iteratedFDeriv_add_apply (f := fun _ => -c0*eps) contDiffAt_const
      (hmuli.of_le (by simp)).contDiffAt,iteratedFDeriv_const_of_ne (by omega : k≠0),Pi.zero_apply,zero_add]
    change ‖iteratedFDeriv ℝ k (fun x => (lam*tau) • normalizedRetractionShift N f.p f.m i x) theta‖≤C
    rw [iteratedFDeriv_const_smul_apply'
      ((normalizedRetractionShift_smooth N f.p f.m hp hm i).of_le (by simp)).contDiffAt,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hl ht)]
    have hlt : lam*tau≤1 := (mul_le_of_le_one_right hl ht1).trans hl1
    exact (mul_le_mul_of_nonneg_left hb (mul_nonneg hl ht)).trans (mul_le_of_le_one_left hC hlt)
  have hcast := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := theta) hv.contDiffAt
    (by simp : (k:ℕ∞ω)≤∞)
  have hof : ‖Complex.ofRealCLM‖≤1 := Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)
  have hvCb : ‖iteratedFDeriv ℝ k (fun x => (v x:ℂ)) theta‖≤C :=
    (hcast.trans (mul_le_of_le_one_left (norm_nonneg _) hof)).trans hvb
  change ‖iteratedFDeriv ℝ k (fun x => (sourceS s,(v x:ℂ),L x)) theta‖≤1+C
  rw [iteratedFDeriv_prodMk (n := ∞) contDiffAt_const (hvC.prodMk L.contDiff).contDiffAt (by simp),
    iteratedFDeriv_const_of_ne (by omega : k≠0),Pi.zero_apply]
  apply (multilinear_prod_norm_le_max _ _).trans
  simp only [norm_zero,max_le_iff]
  refine ⟨by positivity,?_⟩
  rw [iteratedFDeriv_prodMk hvC.contDiffAt L.contDiff.contDiffAt (by simp : (k:ℕ∞ω)≤∞)]
  exact (multilinear_prod_norm_le_max _ _).trans (max_le (by linarith) (by linarith))

/-- Genuine coupled phase jets on the compact-right box. Constants precede
N; the N-dimensional bump is only real-smooth and its occupancy is retained. -/
theorem actual_compact_phase_absolute_jets (d : LocalBranchData) (f : SelectorFunctions)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpper : Function.Periodic f.p (2*Real.pi)) (hmper : Function.Periodic f.m (2*Real.pi))
    (hpv : ∀ x, 0≤f.p x ∧ f.p x≤1) (hmv : ∀ x, 0≤f.m x ∧ f.m x≤1)
    {a b : ℝ} (hmargin : ∀ theta ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos theta|<1)
    (J : ℕ) : ∃ r C : ℝ, 0<r ∧ 0<C ∧
      ∀ N : ℕ, 0<N → ∀ eps tau lam : ℝ, 0≤eps → 0≤tau → tau≤1 → 0≤lam → lam≤1 →
      eps+lam≤r → ∀ theta : Fin N → ℝ, (∀ i, theta i ∈ Icc a b) → ∀ k≤J,
      ‖iteratedFDeriv ℝ k (currentComplexPhase f (Real.exp (-d.c₀*eps)) tau lam
        (radialParameter d.theta eps)) theta‖ ≤ C*N := by
  obtain ⟨r0,B,hr0,hB,hmodel⟩ := compactPhaseModel_real_compact_tube hmargin J
  obtain ⟨A,hA,hret⟩ := periodic_retraction_finite_jets f hp hm hpper hmper J
  let D := 5+d.c₀
  have hD : 0<D := by dsimp [D]; positivity [d.c₀_pos]
  let C := (J.factorial:ℝ)*B*(1+A)^J
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨r0/D,C,div_pos hr0 hD,hC,?_⟩
  intro N hN eps tau lam he ht ht1 hl hl1 hsmall theta htheta k hk
  let z := radialParameter d.theta eps
  let g : Fin N → (Fin N → ℝ) → ℂ × ℂ × ℂ :=
    fun i => currentPhaseAngularPoint f d.c₀ eps tau lam z i
  have hgs (i : Fin N) : ContDiff ℝ ∞ (g i) :=
    currentPhaseAngularPoint_smooth f hp hm d.c₀ eps tau lam z i
  have hpoints (i : Fin N) : AnalyticAt ℂ compactPhaseModel (g i theta) ∧
      ∀ j≤J, ‖iteratedFDeriv ℝ j compactPhaseModel (g i theta)‖≤B := by
    let v := -d.c₀*eps+lam*tau*normalizedRetractionShift N f.p f.m i theta
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have hP0 := occupancy_nonneg (fun l => (hpv (theta l)).1)
    have hP1 := occupancy_le (fun l => (hpv (theta l)).2)
    have hv : |v|≤d.c₀*eps+2*tau*lam := by
      simpa only [v,normalizedRetractionShift,normalizedAngularOccupancy,occupancy,coupledRadialExponent] using
        coupledRadialExponent_lambda_bound d.c₀_pos.le he ht hl
          (hpv (theta i)).1 (hpv (theta i)).2 (hmv (theta i)).1 (hmv (theta i)).2
          (div_nonneg hP0 hn.le) ((div_le_one hn).mpr hP1)
    have htrace := sourceS_radial_to_boundary d eps he
    have htl : tau*lam≤lam := mul_le_of_le_one_left hl ht1
    have hmax : max ‖sourceS z-((1+Real.cos d.thetaB:ℝ):ℂ)‖ ‖(v:ℂ)‖≤D*(eps+lam) := by
      rw [max_le_iff,Complex.norm_real,Real.norm_eq_abs]
      dsimp [D,z]
      constructor <;> nlinarith [mul_nonneg d.c₀_pos.le he,mul_nonneg d.c₀_pos.le hl]
    have hsmall0 : D*(eps+lam)≤r0 := by
      have hh := (le_div_iff₀ hD).mp hsmall
      nlinarith
    obtain ⟨ha,hj⟩ := hmodel (theta i) (htheta i) (sourceS z) (v:ℂ) (hmax.trans hsmall0)
    exact ⟨ha,fun j hjJ => (hj j hjJ).1⟩
  have hcomp (i : Fin N) : ContDiffAt ℝ ∞ (compactPhaseModel ∘ g i) theta :=
    (((hpoints i).1.contDiffAt : ContDiffAt ℂ ∞ compactPhaseModel (g i theta)).restrict_scalars ℝ).comp theta (hgs i).contDiffAt
  have hfb (i : Fin N) : ‖iteratedFDeriv ℝ k (compactPhaseModel ∘ g i) theta‖≤C := by
    have hh := real_model_composition_jet_bound (g i) (hgs i) theta (hpoints i).1 k B (1+A)
      (fun j hj => (hpoints i).2 j (hj.trans hk)) (by
        intro j hj hjk
        have hb := currentPhaseAngularPoint_positive_jet f hp hm d.c₀ eps tau lam z i theta
          ht ht1 hl hl1 A (by linarith) j hj (hret N hN i theta j (hjk.trans hk))
        exact hb.trans (le_self_pow₀ (by linarith : 1≤1+A) (by omega)))
    apply hh.trans
    dsimp [C]
    have hbase : 1≤1+A := by linarith
    gcongr
  have heq : currentComplexPhase f (Real.exp (-d.c₀*eps)) tau lam z =
      (fun x => ∑ i, compactPhaseModel (g i x)) := by
    funext x
    unfold currentComplexPhase
    apply Finset.sum_congr rfl
    intro i _
    exact currentPhaseAngularPoint_source f d.c₀ eps tau lam z i x
  have hcomp' (i : Fin N) : ContDiffAt ℝ k (fun x => compactPhaseModel (g i x)) theta :=
    (hcomp i).of_le (by simp)
  rw [heq,iteratedFDeriv_fun_sum_apply (fun i _ => hcomp' i)]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ k (compactPhaseModel ∘ g i) theta‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hfb i)
    _ = C*N := by simp [mul_comm]

end
end IsingBulk.Tail
