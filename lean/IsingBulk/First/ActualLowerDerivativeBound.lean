import IsingBulk.First.ActualShapeDerivative
import IsingBulk.First.ActualShapeNeighborhood
import IsingBulk.First.ShapeCutoffBounds

/-! Uniform O(1) for each actual derivative order below the first singular
order. The complete derivative numerator is combined before applying the
zero-damping fixed-ball majorant, including derivative order zero. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology

def intrinsicCombinedAmplitude {n : ℕ} (a : OrderedChartData) (j : ℕ)
    (p : ℝ × ShapeSpace n) : ℂ :=
  intrinsicLeadingAmplitude a j p + actualShapeDenominator a p.1 p.2 * intrinsicRemainderAmplitude a j p

theorem intrinsicCombinedAmplitude_uniform_neighborhood {n : ℕ} (a : OrderedChartData) (j : ℕ) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ epsilon : ℝ, ∀ x : ShapeSpace n,
      |epsilon| < r → ‖x‖ < r →
      ContinuousAt (intrinsicCombinedAmplitude a j) (epsilon,x) ∧
      ContinuousAt (fun q : ℝ × ShapeSpace n => actualShapeDenominator a q.1 q.2) (epsilon,x) ∧
      ‖intrinsicCombinedAmplitude a j (epsilon,x)‖ ≤ M := by
  have hcont : ∀ᶠ p : ℝ × ShapeSpace n in 𝓝 (0,0),
      ContinuousAt (intrinsicCombinedAmplitude a j) p ∧
      ContinuousAt (fun q : ℝ × ShapeSpace n => actualShapeDenominator a q.1 q.2) p := by
    filter_upwards [intrinsic_actual_eventual_continuity (n := n) a j] with p hp
    exact ⟨hp.1.add (hp.2.2.mul hp.2.1),hp.2.2⟩
  let M := ‖intrinsicCombinedAmplitude a j (0,(0:ShapeSpace n))‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : ∀ᶠ p : ℝ × ShapeSpace n in 𝓝 (0,0), ‖intrinsicCombinedAmplitude a j p‖ ≤ M :=
    ((hcont.self_of_nhds.1.norm).eventually (Iio_mem_nhds (by dsimp [M]; linarith))).mono
      (fun _ h => h.le)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hcont.and hb)
  refine ⟨r,M,hr,hM,?_⟩
  intro epsilon x he hx
  have hm : (epsilon,x) ∈ ball (0,(0:ShapeSpace n)) r := by
    rw [mem_ball,dist_eq_norm]
    change max ‖epsilon-0‖ ‖x-0‖ < r
    simpa only [sub_zero,Real.norm_eq_abs,max_lt_iff] using And.intro he hx
  exact ⟨(hball hm).1.1,(hball hm).1.2,(hball hm).2⟩

theorem actual_lower_postMean_shape_bound {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (hj : j < k) (a : OrderedChartData)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R B : ℝ, 0 < R ∧ 0 < B ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < R →
        Integrable (fun x => chi x*intrinsicPostMeanDerivative a j epsilon x) ∧
        ‖∫ x : ShapeSpace n, chi x*intrinsicPostMeanDerivative a j epsilon x‖ ≤ B := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsicCombinedAmplitude_uniform_neighborhood (n := n) a j
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  obtain ⟨rE,hrE,hE⟩ := intrinsic_postMean_derivative_expansion (n := n) a j hb
  let R := min rA (min rD rE)
  have hR : 0 < R := lt_min hrA (lt_min hrD hrE)
  have hRA : R ≤ rA := min_le_left _ _
  have hRD : R ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hRE : R ≤ rE := (min_le_right _ _).trans (min_le_right _ _)
  let B := (M/c^(j+1))*∫ x : ShapeSpace n in ball 0 R,
    shapeVandermondeSq x/‖x‖^(2*(j+1))
  refine ⟨R,‖2*(Real.pi:ℂ)‖*|B|+1,hR,by positivity,?_⟩
  intro chi hchi hchib hchis epsilon he heR
  have hdata (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA epsilon x (by rw [abs_of_pos he]; exact heR.trans_le hRA)
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le hRA)
  have hgap (x : ShapeSpace n) (hx : ‖x‖ < R) :=
    hD epsilon x he (heR.trans_le hRD) (hx.trans_le hRD)
  have hh := shape_cutoff_lower_bound hn hdegree hj
    (fun x => intrinsicCombinedAmplitude a j (epsilon,x)) (actualShapeDenominator a epsilon)
    chi R hM.le hc hchi hchib hchis
    (fun x hx => ((hdata x hx).1.comp (f := fun y : ShapeSpace n => (epsilon,y))
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun x hx => ((hdata x hx).2.1.comp (f := fun y : ShapeSpace n => (epsilon,y))
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun x hx => (hdata x hx).2.2)
    (fun x hx => by
      have hg := hgap x (by simpa only [mem_ball,dist_zero_right] using hx)
      nlinarith)
  have heq : (fun x : ShapeSpace n => chi x*intrinsicPostMeanDerivative a j epsilon x) =
      fun x => (2*(Real.pi:ℂ))*((shapeVandermondeSq x:ℂ)*chi x*
        intrinsicCombinedAmplitude a j (epsilon,x)/(actualShapeDenominator a epsilon x)^(j+1)) := by
    funext x
    by_cases hx : chi x = 0
    · simp only [hx,zero_mul,mul_zero,zero_div]
    · have hxr := hchis x hx
      have hdne : actualShapeDenominator a epsilon x ≠ 0 := by
        intro hz
        have hg := hgap x hxr
        rw [hz,norm_zero] at hg
        have hp : 0 < c*(epsilon+‖x‖^2) := mul_pos hc (by positivity)
        linarith
      rw [hE epsilon x he (heR.trans_le hRE) (hxr.trans_le hRE)]
      unfold intrinsicCombinedAmplitude
      rw [pow_succ]
      field_simp [hdne]
  rw [heq]
  refine ⟨hh.1.const_mul _,?_⟩
  rw [integral_const_mul,norm_mul]
  have hnorm : ‖∫ x : ShapeSpace n, (shapeVandermondeSq x:ℂ)*chi x*
      intrinsicCombinedAmplitude a j (epsilon,x)/(actualShapeDenominator a epsilon x)^(j+1)‖ ≤ |B| :=
    hh.2.trans (le_abs_self _)
  exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans (by linarith)

end
end IsingBulk.First
