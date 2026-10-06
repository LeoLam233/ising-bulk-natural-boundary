import IsingBulk.First.ResidueIntegral
import IsingBulk.First.ContourAngular

/-! Compatible angular localization: every x contour remains unweighted,
and the identical fixed y-angle weight survives the actual residue reduction. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- Ordinary iterated angle integrals, without hidden normalization. -/
def multiAngleIntegral : (N : ℕ) → ((Fin N → ℝ) → ℂ) → ℂ
  | 0, f => f Fin.elim0
  | n+1, f => multiAngleIntegral n (fun θ => ∫ u : ℝ in 0..2*Real.pi, f (Fin.cons u θ))

def angleTuple {N : ℕ} (r : ℝ) (θ : Fin N → ℝ) : Fin N → ℂ := fun i => anglePoint r (θ i)
def angleProductJacobian {N : ℕ} (r : ℝ) (θ : Fin N → ℝ) : ℂ := ∏ i, angleJacobian r (θ i)

theorem angleTuple_cons {n : ℕ} (r u : ℝ) (θ : Fin n → ℝ) :
    angleTuple r (Fin.cons u θ) = Fin.cons (anglePoint r u) (angleTuple r θ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem angleProductJacobian_cons {n : ℕ} (r u : ℝ) (θ : Fin n → ℝ) :
    angleProductJacobian r (Fin.cons u θ) = angleJacobian r u * angleProductJacobian r θ := by
  unfold angleProductJacobian
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Exact finite-dimensional bridge from every dx/(2πi) to x dθ/(2π). -/
theorem multiCircleIntegral_eq_angle (r : ℝ) (N : ℕ) (f : (Fin N → ℂ) → ℂ) :
    multiCircleIntegral r N f = multiAngleIntegral N
      (fun θ => angleProductJacobian r θ * f (angleTuple r θ)) := by
  induction N with
  | zero =>
    simp only [multiCircleIntegral, multiAngleIntegral, angleProductJacobian,
      Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [multiCircleIntegral, ih, multiAngleIntegral]
    congr 1
    funext θ
    rw [normalizedCircleIntegral_eq_angle, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [angleProductJacobian_cons, angleTuple_cons]
    ring

/-- w has only y-angle arguments; s, x, and radius are not its arguments. -/
def weightedDoubleFormFactor (N : ℕ) (r : ℝ) (s : ℂ) (w : (Fin N → ℝ) → ℝ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiAngleIntegral N (fun θ => (w θ : ℂ) * angleProductJacobian r θ *
    multiCircleIntegral r N (fun x => doubleDensity s x (angleTuple r θ)))

def weightedReducedFormFactor (N : ℕ) (r : ℝ) (z : ℂ → ℂ) (w : (Fin N → ℝ) → ℝ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiAngleIntegral N (fun θ => (w θ : ℂ) * angleProductJacobian r θ *
    reducedDensity (fun i => z (anglePoint r (θ i))) (angleTuple r θ))

theorem weightedDoubleFormFactor_one (N : ℕ) (r : ℝ) (s : ℂ) :
    weightedDoubleFormFactor N r s (fun _ => 1) = doubleFormFactor N r s := by
  simp only [weightedDoubleFormFactor, doubleFormFactor, Complex.ofReal_one, one_mul]
  rw [multiCircleIntegral_eq_angle]

/-- The physical residue identity with the same arbitrary fixed real y weight. -/
theorem weighted_residue_reduction (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ) (w : (Fin N → ℝ) → ℝ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i)))) :
    weightedDoubleFormFactor N r s w = weightedReducedFormFactor N r z w := by
  unfold weightedDoubleFormFactor weightedReducedFormFactor
  congr 1
  congr 1
  funext θ
  rw [residue_inner_integral hN (h θ)]

end
end IsingBulk.First
