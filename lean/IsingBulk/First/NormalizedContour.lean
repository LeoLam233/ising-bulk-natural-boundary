import IsingBulk.First.ContourDefinitions

/-! Normalized finite-dimensional Cauchy reduction for actual iterated contours. -/
namespace IsingBulk.First
noncomputable section
set_option maxHeartbeats 800000
open Complex Set Metric
open scoped BigOperators

theorem normalizedCircleIntegral_congr {r : ℝ} (hr : 0 ≤ r) {f g : ℂ → ℂ}
    (h : ∀ z, ‖z‖ = r → f z = g z) :
    normalizedCircleIntegral r f = normalizedCircleIntegral r g := by
  unfold normalizedCircleIntegral
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  exact h z (by simpa [mem_sphere_iff_norm] using hz)

theorem normalizedCircleIntegral_const_mul (r : ℝ) (a : ℂ) (f : ℂ → ℂ) :
    normalizedCircleIntegral r (fun z => a * f z) = a * normalizedCircleIntegral r f := by
  simp only [normalizedCircleIntegral, circleIntegral.integral_const_mul]
  ring

theorem normalizedCircleIntegral_cauchy {r : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 r)) (hz : ‖z‖ < r) :
    normalizedCircleIntegral r (fun x => (x-z)⁻¹ * f x) = f z := by
  exact hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (by simpa using hz)

theorem multiCircleIntegral_const_mul (r : ℝ) (N : ℕ) (a : ℂ)
    (f : (Fin N → ℂ) → ℂ) :
    multiCircleIntegral r N (fun x => a * f x) = a * multiCircleIntegral r N f := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [multiCircleIntegral, normalizedCircleIntegral_const_mul]
    exact ih _

theorem multiCircleIntegral_congr {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    {f g : (Fin N → ℂ) → ℂ}
    (h : ∀ x ∈ productCircle N r, f x = g x) :
    multiCircleIntegral r N f = multiCircleIntegral r N g := by
  induction N with
  | zero => exact h _ (fun i => Fin.elim0 i)
  | succ n ih =>
    apply ih
    intro x hx
    apply normalizedCircleIntegral_congr hr
    intro z hz
    apply h
    intro i
    refine Fin.cases hz (fun j => ?_) i
    exact hx j

theorem differentiableAt_cons_head {n : ℕ} (x : Fin n → ℂ) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => (Fin.cons w x : Fin (n+1) → ℂ)) z := by
  apply differentiableAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact differentiableAt_id
  · exact differentiableAt_const (x j)

theorem differentiableAt_cons_tail {n : ℕ} (z : ℂ) (x : Fin n → ℂ) :
    DifferentiableAt ℂ (fun y : Fin n → ℂ => (Fin.cons z y : Fin (n+1) → ℂ)) x := by
  apply differentiableAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact differentiableAt_const z
  · exact differentiableAt_apply j x

/-- Successive residues of the actual product Cauchy kernel, with a holomorphic
numerator on a neighborhood of the whole closed polydisk. -/
theorem multiCircleIntegral_cauchy {r : ℝ} (hr : 0 < r) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) (z : Fin N → ℂ)
    (hz : ∀ i, ‖z i‖ < r)
    (hf : ∀ x ∈ closedPolydisk N r, DifferentiableAt ℂ f x) :
    multiCircleIntegral r N (fun x => (∏ i, (x i-z i)⁻¹) * f x) = f z := by
  induction N with
  | zero =>
    have he : z = Fin.elim0 := Subsingleton.elim _ _
    simp [multiCircleIntegral, he]
  | succ n ih =>
    let z' : Fin n → ℂ := fun i => z i.succ
    let f' : (Fin n → ℂ) → ℂ := fun x => f (Fin.cons (z 0) x)
    have hf' : ∀ x ∈ closedPolydisk n r, DifferentiableAt ℂ f' x := by
      intro x hx
      apply (hf _ ?_).comp x (differentiableAt_cons_tail (z 0) x)
      intro i
      exact Fin.cases (hz 0).le (fun j => hx j) i
    have hreduce : multiCircleIntegral r (n+1) (fun x => (∏ i, (x i-z i)⁻¹) * f x) =
        multiCircleIntegral r n (fun x => (∏ i, (x i-z' i)⁻¹) * f' x) := by
      change multiCircleIntegral r n (fun x => normalizedCircleIntegral r
        (fun w => (∏ i, ((Fin.cons w x : Fin (n+1) → ℂ) i-z i)⁻¹) * f (Fin.cons w x))) = _
      apply multiCircleIntegral_congr hr.le n
      intro x hx
      have hhol : DiffContOnCl ℂ (fun w => f (Fin.cons w x)) (ball 0 r) := by
        apply DifferentiableOn.diffContOnCl_ball (U := closedBall 0 r)
        · intro w hw
          apply DifferentiableAt.differentiableWithinAt
          apply (hf _ ?_).comp w (differentiableAt_cons_head x w)
          intro i
          exact Fin.cases (by simpa using hw) (fun j => (hx j).le) i
        · exact Set.Subset.rfl
      have he : (fun w : ℂ =>
          (∏ i : Fin (n+1), ((Fin.cons w x : Fin (n+1) → ℂ) i-z i)⁻¹) * f (Fin.cons w x)) =
          (fun w : ℂ => (∏ i : Fin n, (x i-z' i)⁻¹) *
            ((w-z 0)⁻¹ * f (Fin.cons w x))) := by
        funext w
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, z']
        ring
      rw [he, normalizedCircleIntegral_const_mul,
        normalizedCircleIntegral_cauchy hhol (hz 0)]
    rw [hreduce, ih f' z' (fun i => hz i.succ) hf']
    change f (Fin.cons (z 0) (fun i => z i.succ)) = f z
    congr 1
    exact Fin.cons_self_tail z

end
end IsingBulk.First
