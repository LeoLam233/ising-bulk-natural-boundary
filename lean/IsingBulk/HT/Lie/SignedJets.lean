import IsingBulk.HT.Lie.SignedTransport
import IsingBulk.Analysis.JetsTheorem

/-!
The HT signed high-order expansion uses exactly the LT semantic term list.
A frozen kernel quotient transfers the already proved recurrence, then
cancels algebraically in every term. In particular it does not enter the
regular coefficient or its uniform jet bound, and no Vandermonde factor
is divided out. The actual signed density is defined before this proof.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open Set Filter IsingBulk.Lie IsingBulk.Jets IsingBulk.Branch
open scoped Topology ContDiff

/-- This ratio is only a proof device on the common regular chart. -/
def kernelSwitch {n : ℕ} (σ : ℂ) (Y Z : ℂ → AngularSpace n → ℂ)
    (s : ℂ) (x : AngularSpace n) : ℂ :=
  signedKernel σ Y Z s x * (simpleKernel Y Z s x)⁻¹

theorem kernelSwitch_regular {n : ℕ} {U : Set ℂ} {R : Set (AngularSpace n)}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ}
    {Y Z : ℂ → AngularSpace n → ℂ} (h : FrozenKernel U R V Y Z)
    (σ : ℂ) (hY : ∀ s ∈ U, ∀ x ∈ R, 1-σ*Y s x ≠ 0)
    (hZ : ∀ s ∈ U, ∀ x ∈ R, 1-σ*Z s x ≠ 0)
    {s : ℂ} (hs : s ∈ U) {x : AngularSpace n} (hx : x ∈ R) :
    DifferentiableAt ℂ (fun t => kernelSwitch σ Y Z t x) s ∧
      DifferentiableAt ℝ (kernelSwitch σ Y Z s) x ∧
      transport V (kernelSwitch σ Y Z) s x = 0 := by
  have hσ := frozenKernel_scale h σ hY hZ
  have hsσ : DifferentiableAt ℂ (fun t => signedKernel σ Y Z t x) s := hσ.parameter hs hx
  have hxσ : DifferentiableAt ℝ (signedKernel σ Y Z s) x := hσ.spatial hs hx
  have hzσ : transport V (signedKernel σ Y Z) s x = 0 := hσ.transport_zero hs hx
  refine ⟨hsσ.mul ((h.parameter hs hx).inv (h.nonzero hs hx)),
    hxσ.mul ((h.spatial hs hx).inv (h.nonzero hs hx)), ?_⟩
  unfold kernelSwitch
  rw [transport_mul V _ _ s x hsσ ((h.parameter hs hx).inv (h.nonzero hs hx))
    hxσ ((h.spatial hs hx).inv (h.nonzero hs hx)), hzσ,
    transport_inv V _ s x (h.parameter hs hx) (h.spatial hs hx) (h.nonzero hs hx),
    h.transport_zero hs hx]
  ring

/-- Construct the unsigned frozen data from the actual branch chart. -/
theorem actualFrozenKernel_of_chart {n : ℕ} (v θ : ℝ) (p q : Fin (n+1))
    (U : Set ℂ) (R : Set (AngularSpace n))
    (hchart : ∀ s ∈ U, ∀ x ∈ R, ActualJetPoint v θ p q s x) :
    FrozenKernel U R (actualField v θ p q) (actualY v θ) (actualZ v θ) := by
  have hG : ∀ s ∈ U, ∀ x ∈ R, ∀ i, angularG v θ (x i) ≠ 0 := by
    intro s hs x hx i hz
    simpa [hz] using (hchart s hs x hx).g_pos i
  have hK : ∀ s ∈ U, ∀ x ∈ R,
      (1-actualY v θ s x)*(1-actualZ v θ s x) ≠ 0 := by
    intro s hs x hx
    rw [← regularKernel_chart s v θ x (hchart s hs x hx).g_pos]
    exact (hchart s hs x hx).kernel_ne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs x hx
    exact differentiableAt_const _
  · intro s hs x hx
    have h := hchart s hs x hx
    exact (actualZ_parameter v θ s x h.s_ne h.re_pos h.im_pos (hG s hs x hx)).differentiableAt
  · intro s hs x hx
    exact (actualY_spatial v θ s x).differentiableAt
  · intro s hs x hx
    have h := hchart s hs x hx
    exact (actualZ_spatial v θ s x h.re_pos h.im_pos).differentiableAt
  · intro s hs x hx
    exact (mul_ne_zero_iff.mp (hK s hs x hx)).1
  · intro s hs x hx
    exact (mul_ne_zero_iff.mp (hK s hs x hx)).2
  · intro s hs x hx
    exact actualY_frozen v θ p q s x (hchart s hs x hx).b_ne
  · intro s hs x hx
    have h := hchart s hs x hx
    exact actualZ_frozen v θ p q s x h.s_ne h.re_pos h.im_pos (hG s hs x hx)

/-- The literal signed semantic term: the LT coefficient and derivative
words are retained; only the actual simple kernel is signed. -/
def signedSourceValue {n : ℕ} (σ : ℂ) (T : SourceJetTerm (n+1))
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  (cutoffJet T.cutoff w x:ℂ) * chartPullback v θ
    (fun t φ => T.coefficient p q (t,φ) * numeratorJet T.numerator Q (t,φ) /
      signedRegularKernel σ t φ) s x

def signedInitialSourceDensity {n : ℕ} (σ : ℂ) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (x : AngularSpace n) : ℂ :=
  (w x:ℂ) * chartPullback v θ (fun t φ => Q (t,φ)/signedRegularKernel σ t φ) s x

def signedSourceTermSum {n : ℕ} (σ : ℂ) (p q : Fin (n+1)) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (j : ℕ) (s : ℂ) (x : AngularSpace n) : ℂ :=
  ((sourceJetTerms p q j).map (fun T => signedSourceValue σ T p q v θ w Q s x)).sum

theorem kernelSwitch_chart {n : ℕ} (σ s : ℂ) (v θ : ℝ) (x : AngularSpace n)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re) :
    kernelSwitch σ (actualY v θ) (actualZ v θ) s x =
      regularKernel s (chartMap v θ s x) /
        signedRegularKernel σ s (chartMap v θ s x) := by
  rw [show chartMap v θ s x = (fun i => chartPhase s v θ (x i)) from rfl,
    regularKernel_chart s v θ x hg, signedRegularKernel_chart σ s v θ x hg]
  simp only [kernelSwitch, signedKernel, simpleKernel, div_eq_mul_inv,
    mul_inv_rev, inv_inv]
  ring

theorem signedSourceValue_eq_switch {n : ℕ} (σ : ℂ) (T : SourceJetTerm (n+1))
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (x : AngularSpace n)
    (h : ActualJetPoint v θ p q s x)
    (hσ : signedRegularKernel σ s (chartMap v θ s x) ≠ 0) :
    signedSourceValue σ T p q v θ w Q s x =
      kernelSwitch σ (actualY v θ) (actualZ v θ) s x *
        T.sourceValue p q v θ w Q s x := by
  rw [kernelSwitch_chart σ s v θ x h.g_pos]
  unfold signedSourceValue SourceJetTerm.sourceValue chartPullback SourceJetTerm.density
  change (cutoffJet T.cutoff w x:ℂ) *
      (chartJacobian v θ s x *
        (T.coefficient p q (s,chartMap v θ s x) *
          numeratorJet T.numerator Q (s,chartMap v θ s x) /
            signedRegularKernel σ s (chartMap v θ s x))) =
    (regularKernel s (chartMap v θ s x)/signedRegularKernel σ s (chartMap v θ s x))*
      ((cutoffJet T.cutoff w x:ℂ)*(chartJacobian v θ s x*
        (T.coefficient p q (s,chartMap v θ s x)*numeratorJet T.numerator Q (s,chartMap v θ s x)/
          regularKernel s (chartMap v θ s x))))
  field_simp [h.kernel_ne, hσ]

theorem signedSourceTermSum_eq_switch {n : ℕ} (σ : ℂ) (p q : Fin (n+1))
    (v θ : ℝ) (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (j : ℕ) (s : ℂ) (x : AngularSpace n) (h : ActualJetPoint v θ p q s x)
    (hσ : signedRegularKernel σ s (chartMap v θ s x) ≠ 0) :
    signedSourceTermSum σ p q v θ w Q j s x =
      kernelSwitch σ (actualY v θ) (actualZ v θ) s x *
        sourceTermSum p q v θ w Q j s x := by
  unfold signedSourceTermSum sourceTermSum
  simp_rw [signedSourceValue_eq_switch σ _ p q v θ w Q s x h hσ]
  exact List.sum_map_mul_left _ _ _

theorem signedSourceTermSum_zero {n : ℕ} (σ : ℂ) (p q : Fin (n+1))
    (v θ : ℝ) (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) :
    signedSourceTermSum σ p q v θ w Q 0 = signedInitialSourceDensity σ v θ w Q := by
  funext s x
  simp [signedSourceTermSum, sourceJetTerms, signedSourceValue,
    SourceJetTerm.coefficient, numeratorJet, directionJet, cutoffJet,
    signedInitialSourceDensity, chartPullback]

/-- Differentiability of the unsigned finite sum is derived term by term;
it is not an additional higher-order hypothesis in the signed recurrence. -/
theorem sourceTermSum_differentiable {n : ℕ} (p q : Fin (n+1)) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (j : ℕ) (s : ℂ) (x : AngularSpace n) (hw : ContDiff ℝ ∞ w)
    (h : ActualJetPoint v θ p q s x) (hQ : AnalyticAt ℂ Q (s,chartMap v θ s x)) :
    DifferentiableAt ℂ (fun t => sourceTermSum p q v θ w Q j t x) s ∧
      DifferentiableAt ℝ (sourceTermSum p q v θ w Q j s) x := by
  have hT := sourceJetTerms_analytic p q j (s,chartMap v θ s x)
    h.coefficient.regular_numerators.1 h.coefficient.regular_numerators.2
  have hd := fun T hmem => SourceJetTerm.sourceValue_differentiable T v θ p q s x w Q hw
    (hT T hmem) hQ h.s_ne h.re_pos h.im_pos h.sin_ne h.slit h.delta_ne h.kernel_ne
  have hV := actualField_differentiable v θ p q s x h.re_pos h.im_pos
    (fun i hz => by simpa [hz] using h.g_pos i) h.sin_ne h.b_ne
  have hf := lieStep_finite_sum (actualField v θ p q)
    ((sourceJetTerms p q j).map (fun T => T.sourceValue p q v θ w Q)) s x hV
    (by
      intro F hF
      obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hF
      exact (hd T hmem).1)
    (by
      intro F hF
      obtain ⟨T,hmem,rfl⟩ := List.mem_map.mp hF
      exact (hd T hmem).2)
  constructor
  · simpa only [sourceTermSum, List.map_map, Function.comp_def] using hf.1
  · change DifferentiableAt ℝ
      (fun y => ((sourceJetTerms p q j).map
        (fun T => T.sourceValue p q v θ w Q s y)).sum) x
    simpa only [List.map_map, Function.comp_def] using hf.2.1

/-- The same finite semantic list realizes the full signed recurrence.
All derivatives of V and div V remain inside lieStep. Uniform coefficient
and list-length estimates are exactly the existing unsigned estimates. -/
theorem signed_sourceJetTerms_all_order_analytic {n : ℕ} (σ : ℂ)
    (p q : Fin (n+1)) (hpq : p ≠ q) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (U : Set ℂ) (R : Set (AngularSpace n))
    (hU : IsOpen U) (hR : IsOpen R) (hw : ContDiff ℝ ∞ w)
    (hchart : ∀ s ∈ U, ∀ x ∈ R, ActualJetPoint v θ p q s x)
    (hσ : ∀ s ∈ U, ∀ x ∈ R, signedRegularKernel σ s (chartMap v θ s x) ≠ 0)
    (hQ : ∀ s ∈ U, ∀ x ∈ R, AnalyticAt ℂ Q (s,chartMap v θ s x)) (j : ℕ) :
    ∀ s ∈ U, ∀ x ∈ R,
      ((lieStep (actualField v θ p q))^[j]
        (signedInitialSourceDensity σ v θ w Q)) s x =
      signedSourceTermSum σ p q v θ w Q j s x := by
  have hK := actualFrozenKernel_of_chart v θ p q U R hchart
  have hS : ∀ s ∈ U, ∀ x ∈ R,
      (1-σ*actualY v θ s x)*(1-σ*actualZ v θ s x) ≠ 0 := by
    intro s hs x hx
    rw [← signedRegularKernel_chart σ s v θ x (hchart s hs x hx).g_pos]
    exact hσ s hs x hx
  have hY : ∀ s ∈ U, ∀ x ∈ R, 1-σ*actualY v θ s x ≠ 0 :=
    fun s hs x hx => (mul_ne_zero_iff.mp (hS s hs x hx)).1
  have hZ : ∀ s ∈ U, ∀ x ∈ R, 1-σ*actualZ v θ s x ≠ 0 :=
    fun s hs x hx => (mul_ne_zero_iff.mp (hS s hs x hx)).2
  have heq (l : ℕ) : ∀ s ∈ U, EqOn
      (signedSourceTermSum σ p q v θ w Q l s)
      (fun x => kernelSwitch σ (actualY v θ) (actualZ v θ) s x *
        sourceTermSum p q v θ w Q l s x) R := by
    intro s hs x hx
    exact signedSourceTermSum_eq_switch σ p q v θ w _ l s x
      (hchart s hs x hx) (hσ s hs x hx)
  induction j with
  | zero =>
    intro s hs x hx
    rw [signedSourceTermSum_zero]
    rfl
  | succ j ih =>
    intro s hs x hx
    have h := hchart s hs x hx
    have hQa := hQ s hs x hx
    have hsum := sourceTermSum_differentiable p q v θ w _ j s x hw h hQa
    have hswitch := kernelSwitch_regular hK σ hY hZ hs hx
    have hV := actualField_differentiable v θ p q s x h.re_pos h.im_pos
      (fun i hz => by simpa [hz] using h.g_pos i) h.sin_ne h.b_ne
    rw [Function.iterate_succ_apply']
    rw [lieStep_congr_on (actualField v θ p q) hU hR ih hs hx]
    rw [lieStep_congr_on (actualField v θ p q) hU hR (heq j) hs hx]
    rw [lieStep_mul_frozen (actualField v θ p q)
      (kernelSwitch σ (actualY v θ) (actualZ v θ))
      (sourceTermSum p q v θ w Q j) s x
      hswitch.1 hsum.1 hswitch.2.1 hsum.2 hV hswitch.2.2]
    rw [sourceTermSum_step p q hpq v θ w _ j s x hw h hQa]
    exact (heq (j+1) s hs hx).symm


/-- The manuscript's numerator is explicitly kept unfactored. -/
theorem signed_sourceJetTerms_all_order {n : ℕ} (σ : ℂ)
    (p q : Fin (n+1)) (hpq : p ≠ q) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (A : ℂ × (Fin (n+1) → ℂ) → ℂ) (U : Set ℂ) (R : Set (AngularSpace n))
    (hU : IsOpen U) (hR : IsOpen R) (hw : ContDiff ℝ ∞ w)
    (hchart : ∀ s ∈ U, ∀ x ∈ R, ActualJetPoint v θ p q s x)
    (hσ : ∀ s ∈ U, ∀ x ∈ R, signedRegularKernel σ s (chartMap v θ s x) ≠ 0)
    (hA : ∀ s ∈ U, ∀ x ∈ R, AnalyticAt ℂ A (s,chartMap v θ s x)) (j : ℕ) :
    ∀ s ∈ U, ∀ x ∈ R,
      ((lieStep (actualField v θ p q))^[j]
        (signedInitialSourceDensity σ v θ w (unfactoredNumerator A))) s x =
      signedSourceTermSum σ p q v θ w (unfactoredNumerator A) j s x := by
  exact signed_sourceJetTerms_all_order_analytic σ p q hpq v θ w
    (unfactoredNumerator A) U R hU hR hw hchart hσ
    (fun s hs x hx => unfactoredNumerator_analytic A _ (hA s hs x hx)) j

end
end IsingBulk.HT.Lie
