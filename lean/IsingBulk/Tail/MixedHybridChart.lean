import IsingBulk.Tail.MixedFrozenPhase
import IsingBulk.Tail.SelectorJacobian
import IsingBulk.Analysis.JetsCoefficientJets
import Mathlib.Topology.MetricSpace.ProperSpace

/-! The mixed residual has no selected-difference pole. The reciprocal
branch slope extends analytically through phi=0; normalized sums isolate
the only linear dimension factor in both nonzero residual coefficients. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def mixedInverseSlope (s φ : ℂ) : ℂ := Complex.sin φ/regularG s φ

theorem mixedInverseSlope_zero (s : ℂ) : mixedInverseSlope s 0=0 := by simp [mixedInverseSlope]

theorem mixedInverseSlope_analytic_base (s : ℂ) (c : ℝ) (hs : s≠0)
    (hS : s+s⁻¹=(1+c:ℂ)) (hc : |c|<1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => mixedInverseSlope z.1 z.2) (s,0) :=
  (show AnalyticAt ℂ (fun z : ℂ × ℂ => Complex.sin z.2) (s,0) by fun_prop).div
    (regularG_analytic_base s c hs hS hc) (regularG_base_ne_zero s c hS hc)

theorem mixedInverseSlope_chart (s : ℂ) (v b : ℝ) (u : ℂ)
    (hg : 0<(angularG v b u).re) :
    mixedInverseSlope s (chartPhase s v b u)=(chartB s v b u)⁻¹ := by
  unfold mixedInverseSlope chartB
  rw [regularG_chartPhase s v b u hg,inv_div]

/-- Coordinates are reciprocal branch slope, compact slope, normalized A,
and normalized D. The functions contain no singular difference variable. -/
abbrev MixedResidualData := ℂ × ℂ × ℂ × ℂ

def mixedResidualCore (v : MixedResidualData) : ℂ := -(v.2.2.2+v.2.1*v.2.2.1)/(1-v.2.1*v.1)
def mixedCompactCore (v : MixedResidualData) : ℂ := -v.2.2.1+v.1*mixedResidualCore v

theorem mixedResidualCore_analyticAt {v : MixedResidualData} (hd : 1-v.2.1*v.1≠0) :
    AnalyticAt ℂ mixedResidualCore v := by
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact hd

theorem mixedCompactCore_analyticAt {v : MixedResidualData} (hd : 1-v.2.1*v.1≠0) :
    AnalyticAt ℂ mixedCompactCore v := by
  exact (show AnalyticAt ℂ (fun t : MixedResidualData => -t.2.2.1) v by fun_prop).add
    (analyticAt_fst.mul (mixedResidualCore_analyticAt hd))

theorem mixed_residual_normalized {N : ℕ} (hN : 0<N) (β b A D : ℂ) :
    -(D+b*A)/(1-b*β)=(N:ℂ)*mixedResidualCore (β,b,A/(N:ℂ),D/(N:ℂ)) := by
  have hn : (N:ℂ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  unfold mixedResidualCore
  field_simp

theorem mixed_compact_normalized {N : ℕ} (hN : 0<N) (β b A D : ℂ) :
    -A-β*(D+b*A)/(1-b*β)=(N:ℂ)*mixedCompactCore (β,b,A/(N:ℂ),D/(N:ℂ)) := by
  have hn : (N:ℂ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  unfold mixedCompactCore mixedResidualCore
  field_simp
  ring

theorem mixedResidualCore_norm_le {v : MixedResidualData} {B : ℝ}
    (hB : 0≤B) (hb : ‖v.2.1‖≤B) (hA : ‖v.2.2.1‖≤B) (hD : ‖v.2.2.2‖≤B)
    (hsep : ‖v.2.1*v.1‖≤(1/4:ℝ)) :
    ‖mixedResidualCore v‖≤(4/3:ℝ)*(B+B^2) := by
  have hg := mixed_denominator_margin hsep
  have hn : ‖v.2.2.2+v.2.1*v.2.2.1‖≤B+B^2 := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,pow_two]
    exact add_le_add hD (mul_le_mul hb hA (norm_nonneg _) hB)
  unfold mixedResidualCore
  rw [norm_div,norm_neg]
  exact (div_le_div₀ (by positivity) hn (by norm_num : (0:ℝ)<3/4) hg).trans_eq (by ring)

theorem compact_finite_analytic_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Set E) (hK : IsCompact K) (F : E → ℂ) (hF : ∀ x∈K,AnalyticAt ℂ F x) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ x∈K,∀ k≤j,‖iteratedFDeriv ℂ k F x‖≤C := by
  have hc (k : ℕ) : ContinuousOn (iteratedFDeriv ℂ k F) K := by
    intro x hx
    exact ((hF x hx).contDiffAt.continuousAt_iteratedFDeriv (n := ⊤) (by simp)).continuousWithinAt
  have hb (k : ℕ) : ∃ C : ℝ,0<C ∧ ∀ x∈K,‖iteratedFDeriv ℂ k F x‖≤C := by
    obtain ⟨C,hC,hbound⟩ := (hK.image_of_continuousOn (hc k)).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx => hbound _ ⟨x,hx,rfl⟩⟩
  choose C hC hbound using hb
  refine ⟨∑ k∈Finset.range (j+1),C k,Finset.sum_pos (fun k _ => hC k) ⟨0,by simp⟩,?_⟩
  intro x hx k hk
  exact (hbound k x hx).trans (Finset.single_le_sum (fun l _ => (hC l).le)
    (Finset.mem_range.mpr (by omega)))

def mixedResidualCompact (B : ℝ) : Set MixedResidualData :=
  Metric.closedBall 0 B ∩ {v | (3/4:ℝ)≤‖1-v.2.1*v.1‖}

theorem mixedResidualCompact_isCompact (B : ℝ) : IsCompact (mixedResidualCompact B) :=
  (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const (by fun_prop))

/-- The finite-dimensional coefficient bound is uniform before N. Actual
normalized sums and their coupled jets must be attached separately. -/
theorem mixed_residual_finite_jets (B : ℝ) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ v∈mixedResidualCompact B,∀ k≤j,
      ‖iteratedFDeriv ℂ k mixedResidualCore v‖≤C ∧
      ‖iteratedFDeriv ℂ k mixedCompactCore v‖≤C := by
  have hgap (v : MixedResidualData) (hv : v∈mixedResidualCompact B) : 1-v.2.1*v.1≠0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<3/4) hv.2))
  obtain ⟨C,hC,hCb⟩ := compact_finite_analytic_jets _ (mixedResidualCompact_isCompact B)
    mixedResidualCore (fun v hv => mixedResidualCore_analyticAt (hgap v hv)) j
  obtain ⟨D,hD,hDb⟩ := compact_finite_analytic_jets _ (mixedResidualCompact_isCompact B)
    mixedCompactCore (fun v hv => mixedCompactCore_analyticAt (hgap v hv)) j
  exact ⟨max C D,lt_of_lt_of_le hC (le_max_left _ _),fun v hv k hk =>
    ⟨(hCb v hv k hk).trans (le_max_left _ _),(hDb v hv k hk).trans (le_max_right _ _)⟩⟩

def mixedPhaseJacobianCoefficient (s y : ℂ) : ℂ :=
  (y-y⁻¹)/(2*Complex.sin (mixedSourcePhase s y))

def mixedHybridJacobian {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ := fun i k =>
  if i∈J then mixedPhaseJacobianCoefficient s (deformedPoint f r τ lam θ i)*angularJacobian f τ lam θ i k
  else if i=k then 1 else 0

def mixedHybridMap {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  if i∈J then mixedContourPhase f r τ lam s θ i else (θ i:ℂ)

theorem mixedHybridMap_coordinate {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (k i : Fin N)
    (hp : ∀ j,DifferentiableAt ℝ f.p (θ j)) (hm : ∀ j,DifferentiableAt ℝ f.m (θ j))
    (hW : ∀ j∈J,0<(sourceW s (deformedPoint f r τ lam θ j)).im) :
    coordDeriv (fun x => mixedHybridMap J f r τ lam s x i) θ k=mixedHybridJacobian J f r τ lam s θ i k := by
  by_cases hi : i∈J
  · simp only [mixedHybridMap,mixedHybridJacobian,hi,ite_true]
    exact (mixedContourPhase_coordinate f hr τ lam s θ k i hp hm (hW i hi)).deriv
  · simp only [mixedHybridMap,mixedHybridJacobian,hi,ite_false,coordDeriv]
    by_cases hik : i=k
    · subst i
      simp only [Function.update_self,ite_true]
      convert (Complex.ofRealCLM.hasDerivAt (x := θ k)).deriv using 1
      · congr 1
      · rfl
    · simp [hik]

/-- The full occupancy off-diagonal block is retained. Its determinant
cancels by the actual rank-one/plateau identity, not by deleting entries. -/
theorem mixedHybridJacobian_det {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hplateau : ∀ i∈J,f.m (θ i)=1 ∧ deriv f.p (θ i)=0 ∧ deriv f.m (θ i)=0)
    (hb : ∀ i∈J,mixedSourceSlope s (deformedPoint f r τ lam θ i)≠0) :
    (mixedHybridJacobian J f r τ lam s θ).det =
      ∏ i∈J,mixedSourceSlope s (deformedPoint f r τ lam θ i) := by
  let y := deformedPoint f r τ lam θ
  let d := fun i => if i∈J then mixedSourceSlope s (y i) else 1
  let u := fun i => if i∈J then mixedPhaseJacobianCoefficient s (y i)*(lam*τ/(2*N):ℝ) else 0
  let v := fun i => ((deriv f.p (θ i):ℝ):ℂ)
  have hd (i : Fin N) : d i≠0 := by
    by_cases hi : i∈J
    · simpa [d,hi] using hb i hi
    · simp [d,hi]
  have huv (i : Fin N) : u i*v i=0 := by
    by_cases hi : i∈J
    · simp [u,v,hi,(hplateau i hi).2.1]
    · simp [u,hi]
  have he : mixedHybridJacobian J f r τ lam s θ =
      (fun i k => (if i=k then d i else 0)+u i*v k) := by
    ext i k
    by_cases hi : i∈J
    · obtain ⟨hmi,hpi,hmi'⟩ := hplateau i hi
      by_cases hik : i=k
      · subst k
        simp only [mixedHybridJacobian,hi,ite_true,angularJacobian,retractionJacobian,hpi,hmi',hmi,
          mul_zero,add_zero,Complex.ofReal_zero,d,u,v,mixedPhaseJacobianCoefficient,mixedSourceSlope]
        ring
      · simp only [mixedHybridJacobian,hi,ite_true,angularJacobian,retractionJacobian,hik,ite_false,hmi,
          zero_add,d,u,v,mixedPhaseJacobianCoefficient,mixedSourceSlope,mul_one]
        push_cast
        ring
    · simp [mixedHybridJacobian,hi,d,u]
  rw [he,diagonal_rankOne_det d u v hd huv]
  simp [d,y]

theorem mixedHybridJacobian_zero_det {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ : ℝ) (s : ℂ) (θ : Fin N → ℝ) :
    (mixedHybridJacobian J f r τ 0 s θ).det =
      ∏ i∈J,mixedSourceSlope s (deformedPoint f r τ 0 θ i) := by
  have he : mixedHybridJacobian J f r τ 0 s θ =
      Matrix.diagonal (fun i => if i∈J then mixedSourceSlope s (deformedPoint f r τ 0 θ i) else 1) := by
    ext i k
    by_cases hi : i∈J <;> by_cases hik : i=k
    · subst k
      simp only [mixedHybridJacobian,hi,ite_true,angularJacobian,retractionJacobian,
        zero_mul,zero_div,Complex.ofReal_zero,add_zero,Matrix.diagonal_apply_eq,
        mixedPhaseJacobianCoefficient,mixedSourceSlope]
      ring
    · simp [mixedHybridJacobian,hi,hik,angularJacobian,retractionJacobian]
    · subst k
      simp [mixedHybridJacobian,hi]
    · simp [mixedHybridJacobian,hi,hik]
  rw [he,Matrix.det_diagonal]
  simp

end
end IsingBulk.Tail
