import IsingBulk.Tail.PairingIntegralBound

/-! Vertex weights are distributed over actual matchings without division.
This remains valid when a weight vanishes. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory

variable {α E : Type*}

theorem pairingWeight_diagonal (c : α → ℝ) (w : α → α → ℝ)
    (M : List (α × α)) :
    pairingWeight (fun a b => c a*c b*w a b) M =
      ((pairingLabels M).map c).prod * pairingWeight w M := by
  induction M with
  | nil => simp [pairingWeight,pairingLabels]
  | cons p M ih =>
    simp only [pairingWeight,List.map_cons,List.prod_cons] at ih ⊢
    simp only [pairingLabels,List.flatMap_cons,List.map_append,List.prod_append,
      List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]
    rw [ih]
    simp only [pairingLabels]
    ring

theorem pairingMajorant_diagonal (c : α → ℝ) (w : α → α → ℝ)
    (n : ℕ) (xs : List α) (hlen : xs.length=2*n) :
    pairingMajorant (fun a b => c a*c b*w a b) n xs =
      (xs.map c).prod * pairingMajorant w n xs := by
  unfold pairingMajorant
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro M hM
  rw [pairingWeight_diagonal]
  rw [((perfectPairings_labels_perm n xs hlen M hM).map c).prod_eq]

theorem weighted_labelPfaffian_le (c : α → ℝ) (hc : ∀ a, 0 ≤ c a)
    (A : α → α → ℂ) (n : ℕ) (xs : List α) (hlen : xs.length=2*n) :
    (xs.map c).prod * ‖labelPfaffian A n xs‖ ≤
      pairingMajorant (fun a b => c a*c b*‖A a b‖) n xs := by
  rw [pairingMajorant_diagonal c _ n xs hlen]
  apply mul_le_mul_of_nonneg_left
  · exact labelPfaffian_norm_le_pairings A (fun a b => ‖A a b‖)
      (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl) n xs
  · exact List.prod_nonneg (by simpa only [List.forall_mem_map] using fun a (_ : a ∈ xs) => hc a)

variable [MeasurableSpace E]

theorem integral_weighted_labelPfaffian_le (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (c : E → ℝ) (hc : ∀ x, 0 ≤ c x) (A : E → E → ℂ)
    (hpair : Integrable (fun v : Fin 2 → E => c (v 0)*c (v 1)*‖A (v 0) (v 1)‖)
      (Measure.pi (fun _ => μ)))
    (hmeas : AEStronglyMeasurable (fun x : Fin (2*n) → E =>
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (fun a b => A (x a) (x b)) n (List.finRange (2*n))‖)
      (Measure.pi (fun _ => μ))) :
    (∫ x : Fin (2*n) → E,
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (fun a b => A (x a) (x b)) n (List.finRange (2*n))‖
      ∂Measure.pi (fun _ => μ)) ≤
      (matchingCount n:ℝ)*(∫ v : Fin 2 → E,
        c (v 0)*c (v 1)*‖A (v 0) (v 1)‖ ∂Measure.pi (fun _ => μ))^n := by
  have hG := pairingMajorant_integrable n μ (fun x y => c x*c y*‖A x y‖) hpair
  have hbound (x : Fin (2*n) → E) := weighted_labelPfaffian_le
    (fun a => c (x a)) (fun a => hc (x a)) (fun a b => A (x a) (x b))
    n (List.finRange (2*n)) (by simp)
  have hnonneg (x : Fin (2*n) → E) : 0 ≤
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (fun a b => A (x a) (x b)) n (List.finRange (2*n))‖ := by
    apply mul_nonneg _ (norm_nonneg _)
    exact List.prod_nonneg (by simpa only [List.forall_mem_map] using
      fun a (_ : a ∈ List.finRange (2*n)) => hc (x a))
  have hi := hG.mono' hmeas (Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hnonneg x)]
    exact hbound x))
  exact (integral_mono hi hG hbound).trans_eq
    (pairingMajorant_integral n μ (fun x y => c x*c y*‖A x y‖) hpair)


theorem integral_coupled_weighted_labelPfaffian_le (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (c : E → ℝ) (hc : ∀ x, 0 ≤ c x)
    (A : (Fin (2*n) → E) → Fin (2*n) → Fin (2*n) → ℂ)
    (k : E → E → ℝ) (hk : ∀ x y, 0 ≤ k x y)
    (hA : ∀ x a b, ‖A x a b‖ ≤ k (x a) (x b))
    (hpair : Integrable (fun v : Fin 2 → E => c (v 0)*c (v 1)*k (v 0) (v 1))
      (Measure.pi (fun _ => μ)))
    (hmeas : AEStronglyMeasurable (fun x : Fin (2*n) → E =>
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (A x) n (List.finRange (2*n))‖) (Measure.pi (fun _ => μ))) :
    (∫ x : Fin (2*n) → E,
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (A x) n (List.finRange (2*n))‖ ∂Measure.pi (fun _ => μ)) ≤
      (matchingCount n:ℝ)*(∫ v : Fin 2 → E,
        c (v 0)*c (v 1)*k (v 0) (v 1) ∂Measure.pi (fun _ => μ))^n := by
  have hG := pairingMajorant_integrable n μ (fun x y => c x*c y*k x y) hpair
  have hcprod (x : Fin (2*n) → E) :
      0 ≤ ((List.finRange (2*n)).map (fun a => c (x a))).prod :=
    List.prod_nonneg (by simpa only [List.forall_mem_map] using
      fun a (_ : a ∈ List.finRange (2*n)) => hc (x a))
  have hbound (x : Fin (2*n) → E) :
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (A x) n (List.finRange (2*n))‖ ≤
      pairingMajorant (fun a b => c (x a)*c (x b)*k (x a) (x b)) n (List.finRange (2*n)) := by
    rw [pairingMajorant_diagonal (fun a => c (x a)) _ n _ (by simp)]
    exact mul_le_mul_of_nonneg_left
      (labelPfaffian_norm_le_pairings (A x) (fun a b => k (x a) (x b))
        (fun a b => hk (x a) (x b)) (hA x) n _) (hcprod x)
  have hi := hG.mono' hmeas (Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hcprod x) (norm_nonneg _))]
    exact hbound x))
  exact (integral_mono hi hG hbound).trans_eq
    (pairingMajorant_integral n μ (fun x y => c x*c y*k x y) hpair)

theorem integrable_coupled_weighted_labelPfaffian (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (c : E → ℝ) (hc : ∀ x, 0 ≤ c x)
    (A : (Fin (2*n) → E) → Fin (2*n) → Fin (2*n) → ℂ)
    (k : E → E → ℝ) (hk : ∀ x y, 0 ≤ k x y)
    (hA : ∀ x a b, ‖A x a b‖ ≤ k (x a) (x b))
    (hpair : Integrable (fun v : Fin 2 → E => c (v 0)*c (v 1)*k (v 0) (v 1))
      (Measure.pi (fun _ => μ)))
    (hmeas : AEStronglyMeasurable (fun x : Fin (2*n) → E =>
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (A x) n (List.finRange (2*n))‖) (Measure.pi (fun _ => μ))) :
    Integrable (fun x : Fin (2*n) → E =>
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (A x) n (List.finRange (2*n))‖) (Measure.pi (fun _ => μ)) := by
  have hG := pairingMajorant_integrable n μ (fun x y => c x*c y*k x y) hpair
  have hcprod (x : Fin (2*n) → E) :
      0 ≤ ((List.finRange (2*n)).map (fun a => c (x a))).prod :=
    List.prod_nonneg (by simpa only [List.forall_mem_map] using
      fun a (_ : a ∈ List.finRange (2*n)) => hc (x a))
  have hbound (x : Fin (2*n) → E) :
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (A x) n (List.finRange (2*n))‖ ≤
      pairingMajorant (fun a b => c (x a)*c (x b)*k (x a) (x b)) n (List.finRange (2*n)) := by
    rw [pairingMajorant_diagonal (fun a => c (x a)) _ n _ (by simp)]
    exact mul_le_mul_of_nonneg_left
      (labelPfaffian_norm_le_pairings (A x) (fun a b => k (x a) (x b))
        (fun a b => hk (x a) (x b)) (hA x) n _) (hcprod x)
  have hi := hG.mono' hmeas (Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hcprod x) (norm_nonneg _))]
    exact hbound x))
  exact hi

end
end IsingBulk.Tail
