import IsingBulk.Analysis.JetsScalarBounds

/-! Polynomial dimension bounds for the actual regular field numerators. -/
namespace IsingBulk.Jets
noncomputable section

theorem ScalarBounds.lift_a {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z J C) (i : Fin N) :
    JetBound (fun t : ℂ × (Fin N → ℂ) => regularA t.1 (t.2 i)) z J C :=
  (h.a i).comp (scalarCoordinate i) (scalarCoordinate_norm i)

theorem ScalarBounds.lift_pair {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z J C) (a : Fin 4) :
    JetBound (fun t : ℂ × (Fin N → ℂ) => pairFactor a (t.1,t.2 p,t.2 q)) z J C :=
  (h.pair a).comp (pairCoordinate p q) (pairCoordinate_norm p q)

theorem ScalarBounds.a_sum {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z J C) :
    JetBound (fun t : ℂ × (Fin N → ℂ) => aSum t.1 t.2) z J (N*C) :=
  ⟨Finset.analyticAt_fun_sum _ (fun i _ => (h.lift_a i).analytic),by
    have := h.one_le; positivity,
    fun k hk => aSum_jet_bound z k C (fun i => (h.a i).analytic)
      (fun i => (h.a i).bound k hk)⟩

theorem ScalarBounds.delta {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z J C) : JetBound (selectedDifferenceCLM p q) z J C :=
  h.lift_pair 3

theorem ScalarBounds.mono {N J K : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z J C) (hK : K ≤ J) : ScalarBounds p q z K C :=
  ⟨h.one_le,h.coefficient,fun i => (h.a i).mono hK le_rfl,
    fun a => (h.pair a).mono hK le_rfl⟩

theorem ScalarBounds.field {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z J C) (hN : 1 ≤ N) (i : Fin N) :
    JetBound (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2)
      z J (3*2^J*C^2*N) := by
  have hb := (((h.lift_a i).mul h.delta).add
    ((h.a_sum.mul (h.lift_pair 1)).ite (i=p))).sub
    ((h.a_sum.mul (h.lift_pair 2)).ite (i=q))
  have he : (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2) =
      (fun t => regularA t.1 (t.2 i)*selectedDifferenceCLM p q t+
        (if i=p then aSum t.1 t.2*pairFactor 1 (t.1,t.2 p,t.2 q) else 0)-
        (if i=q then aSum t.1 t.2*pairFactor 2 (t.1,t.2 p,t.2 q) else 0)) := by
    funext t
    simp only [fieldRegularNumerator,pairFactor_one,pairFactor_two]
    change _ = regularA t.1 (t.2 i)*(t.2 q-t.2 p)+_-_
    split_ifs <;> ring
  rw [he]
  apply hb.mono le_rfl
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hC : 0 ≤ C := zero_le_one.trans h.one_le
  have hpos : 0 ≤ (2:ℝ)^J*C*C := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hNr hpos]

theorem ScalarBounds.residual {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z J C) (i : Fin N) :
    JetBound (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2)
      z J (3*2^J*C^2*N) := by
  have hb := ((h.a_sum.neg.mul (h.lift_pair 0)).ite (i=p)).add
    ((h.a_sum.mul (h.lift_pair 0)).ite (i=q))
  apply hb.mono le_rfl
  have hC : 0 ≤ C := zero_le_one.trans h.one_le
  have hpos : 0 ≤ (2:ℝ)^J*C^2*N := by positivity
  nlinarith

theorem ScalarBounds.divergence {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z (J+1) C) :
    JetBound (divergenceRegularNumerator p q) z J
      (2^J*(C+2)*(3*2^(J+1)*C^2)*N^2) := by
  let K : ℝ := 3*2^(J+1)*C^2*N
  have hC : 0 ≤ C := zero_le_one.trans h.one_le
  have hb : ∀ i, JetBound
      (poleDerivativeNumerator (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2)
        (selectedDifferenceCLM p q) (spatialDirection i)) z J (2^J*C*K+2^J*K*2) := by
    intro i
    have hR : JetBound (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2)
        z (J+1) K := h.residual i
    exact ((h.delta.mono (by omega) le_rfl).mul (hR.direction _ (spatialDirection_norm_le i))).sub
      ((hR.mono (by omega) le_rfl).mul
        ((JetBound.const (selectedDifferenceCLM p q (spatialDirection i)) z J).mono le_rfl
          (selectedDifference_direction_bound p q i)))
  have hsum := JetBound.sum hb (by dsimp [K]; positivity)
  have he : (2:ℝ)^J*(C+2)*(3*2^(J+1)*C^2)*N^2 =
      N*(2^J*C*K+2^J*K*2) := by dsimp [K]; ring
  rw [he]
  exact hsum

def fieldBoundConstant (J : ℕ) (C : ℝ) : ℝ :=
  2+C+3*2^(J+1)*C^2+2^J*(C+2)*(3*2^(J+1)*C^2)

/-- One common polynomial bound; all inputs are actual low-dimensional
source factors. One extra derivative supplies the divergence numerator. -/
theorem ScalarBounds.all_fields {N J : ℕ} {p q : Fin N} {z : ℂ × (Fin N → ℂ)} {C : ℝ}
    (h : ScalarBounds p q z (J+1) C) (hN : 1 ≤ N) :
    2 ≤ fieldBoundConstant J C ∧
    JetBound (selectedDifferenceCLM p q) z J (fieldBoundConstant J C*N^2) ∧
    (∀ i, JetBound (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2)
      z J (fieldBoundConstant J C*N^2)) ∧
    (∀ i, JetBound (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2)
      z J (fieldBoundConstant J C*N^2)) ∧
    JetBound (divergenceRegularNumerator p q) z J (fieldBoundConstant J C*N^2) := by
  let K : ℝ := 3*2^(J+1)*C^2
  let D : ℝ := 2^J*(C+2)*K
  have hC : 0 ≤ C := zero_le_one.trans h.one_le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : fieldBoundConstant J C = 2+C+K+D := rfl
  have hBC : C ≤ fieldBoundConstant J C := by rw [hB]; linarith
  have hBK : K ≤ fieldBoundConstant J C := by rw [hB]; linarith
  have hBD : D ≤ fieldBoundConstant J C := by rw [hB]; linarith
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₂ : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ hN₁
  have hNN : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  refine ⟨by rw [hB]; linarith,?_,?_,?_,?_⟩
  · exact h.delta.mono (by omega)
      (hBC.trans (le_mul_of_one_le_right (by rw [hB]; positivity) hN₂))
  · intro i
    exact (h.field hN i).mono (by omega)
      ((mul_le_mul_of_nonneg_right hBK (by positivity)).trans
        (mul_le_mul_of_nonneg_left hNN (by rw [hB]; positivity)))
  · intro i
    exact (h.residual i).mono (by omega)
      ((mul_le_mul_of_nonneg_right hBK (by positivity)).trans
        (mul_le_mul_of_nonneg_left hNN (by rw [hB]; positivity)))
  · exact h.divergence.mono le_rfl (mul_le_mul_of_nonneg_right hBD (sq_nonneg _))

end
end IsingBulk.Jets
