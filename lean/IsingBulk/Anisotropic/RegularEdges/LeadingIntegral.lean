import IsingBulk.Anisotropic.RegularEdges.LeadingConstrained
import IsingBulk.Anisotropic.RegularEdges.LeadingDerivative
import IsingBulk.First.ShapeMeasure

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter Metric MeasureTheory
open scoped Topology BigOperators

def edgeFreeShape {n : ℕ} (q : Fin n→ℝ) : ShapeSpace n :=
  shapeCoordinateEquiv n (WithLp.toLp 2 q)

@[simp] theorem edgeFreeShape_apply {n : ℕ} (q : Fin n→ℝ) (i : Fin (n+1)) :
    (edgeFreeShape q).1 i=shapeExtend q i := rfl

@[simp] theorem edgeFreeShape_zero (n : ℕ) : edgeFreeShape (0:Fin n→ℝ)=0 := by
  simp [edgeFreeShape]

theorem edgeFreeShape_continuous (n : ℕ) : Continuous (@edgeFreeShape n) :=
  (shapeCoordinateEquiv n).toContinuousLinearEquiv.continuous.comp (PiLp.continuous_toLp 2 _)

def edgeCenteredCube (n : ℕ) : Set (Fin n→ℝ) :=
  Icc (fun _ => -Real.pi) (fun _ => Real.pi)

def edgeFullDerivativeIntegral {n : ℕ} (b : ℝ) (B S : ℂ→ℂ) (j : ℕ) (u : ℂ) : ℂ :=
  ∫ q in edgeCenteredCube n,edgeConstrainedJet b B S j (u,q)

def edgeComplementDerivativeIntegral {n : ℕ} (b : ℝ) (B S : ℂ→ℂ)
    (j : ℕ) (R : ℝ) (u : ℂ) : ℂ :=
  ∫ q in edgeCenteredCube n,(1-edgeShapeCutoff R (edgeFreeShape q))*edgeConstrainedJet b B S j (u,q)

/-- The literal constrained local integral has exactly the intrinsic Jacobian, not an arbitrary factor. -/
theorem edge_local_derivative_integral_eq {n j : ℕ} (b : ℝ) (B S : ℂ→ℂ)
    {R : ℝ} (hR : 0<R) (hRπ : R≤Real.pi) (t : ℝ) :
    (∫ q in edgeCenteredCube n,edgeShapeCutoff R (edgeFreeShape q)*
      edgeConstrainedJet b B S j (Complex.I*(t:ℂ)^2,q))=
        (Real.sqrt (n+1))⁻¹ • edgeActualLocalDerivativeIntegral (n := n) b B S j R t := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_shapeExtend n (fun x => edgeShapeCutoff R x*
      iteratedDeriv j (fun u => edgeAngularDensity b B S u (fun i => x.1 i)) (Complex.I*(t:ℂ)^2))
  · intro q hq
    have hz : edgeShapeCutoff R (edgeFreeShape q)=0 := by
      by_contra hh
      have hx := (edgeShapeCutoff_properties (n := n) hR).2.2.2 _ hh
      apply hq
      constructor <;> intro i
      · have ha := PiLp.norm_apply_le (edgeFreeShape q).1 i.castSucc
        rw [Real.norm_eq_abs,edgeFreeShape_apply,shapeExtend_castSucc] at ha
        exact (abs_le.mp (ha.trans (hx.le.trans hRπ))).1
      · have ha := PiLp.norm_apply_le (edgeFreeShape q).1 i.castSucc
        rw [Real.norm_eq_abs,edgeFreeShape_apply,shapeExtend_castSucc] at ha
        exact (abs_le.mp (ha.trans (hx.le.trans hRπ))).2
    simp only [hz,zero_mul]

/-- The entire compact angular complement has bounded fixed-order jets in a full complex neighborhood. -/
theorem edgeComplementDerivativeIntegral_bounded {n : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) {R : ℝ} (hR : 0<R) (j : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ u in 𝓝 (0:ℂ),‖edgeComplementDerivativeIntegral (n := n) b B S j R u‖≤C := by
  let U : Set (Fin n→ℝ) := {q | ‖edgeFreeShape q‖<R/4}
  have hU : IsOpen U := isOpen_lt (edgeFreeShape_continuous n).norm continuous_const
  have h0 : (0:Fin n→ℝ)∈U := by simp [U]; positivity
  obtain ⟨C,hC,hev⟩ := edgeConstrainedJet_away_bound hb hB hBi hS hS0 hU h0 j
  refine ⟨(2*C)*volume.real (edgeCenteredCube n),by positivity,?_⟩
  filter_upwards [hev] with u hu
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro q hq
  by_cases hqU : q∈U
  · have he : edgeShapeCutoff R (edgeFreeShape q)=1 :=
      edgeShapeCutoff_eq_one hR (le_of_lt hqU)
    simp only [he,sub_self,zero_mul,norm_zero]
    positivity
  · rw [norm_mul]
    have hw : ‖1-edgeShapeCutoff R (edgeFreeShape q)‖≤2 := by
      calc
        _ ≤ ‖(1:ℂ)‖+‖edgeShapeCutoff R (edgeFreeShape q)‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith [(edgeShapeCutoff_properties (n := n) hR).2.2.1 (edgeFreeShape q)]
    exact mul_le_mul hw (hu q (fun i => ⟨hq.1 i,hq.2 i⟩) hqU).2 (norm_nonneg _) (by norm_num)

end
end IsingBulk.Anisotropic.RegularEdges
