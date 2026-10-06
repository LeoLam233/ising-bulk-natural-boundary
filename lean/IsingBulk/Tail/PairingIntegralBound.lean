import IsingBulk.Tail.PairingCoordinateEquiv
import IsingBulk.Tail.MatchingIntegralFactorization

/-! All matchings in the actual Pfaffian expansion factor as genuine
independent-coordinate integrals. The finite integral sum and integrability
are proved explicitly; no per-matching integration certificate is assumed. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory
open scoped BigOperators

variable {E : Type*} [MeasurableSpace E]

omit [MeasurableSpace E] in
theorem pairingWeight_comp_eq {n : ℕ} (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) (f : E → E → ℝ)
    (x : Fin (2*n) → E) :
    pairingWeight (fun a b => f (x a) (x b)) M =
      ∏ i : Fin n, f (x (matchingCoordinateEquiv M hM (i,0)))
        (x (matchingCoordinateEquiv M hM (i,1))) := by
  rw [pairingWeight_eq_prod_entries M hM]
  apply Finset.prod_congr rfl
  intro i hi
  rw [matchingCoordinateEquiv_zero,matchingCoordinateEquiv_one]

theorem pairingWeight_integral {n : ℕ} (μ : Measure E) [SigmaFinite μ]
    (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) (f : E → E → ℝ) :
    (∫ x : Fin (2*n) → E, pairingWeight (fun a b => f (x a) (x b)) M
      ∂Measure.pi (fun _ => μ)) =
      (∫ v : Fin 2 → E, f (v 0) (v 1) ∂Measure.pi (fun _ => μ))^n := by
  simp_rw [pairingWeight_comp_eq M hM]
  exact arbitrary_pairing_integral n μ (matchingCoordinateEquiv M hM) (fun v => f (v 0) (v 1))

theorem pairingWeight_integrable {n : ℕ} (μ : Measure E) [SigmaFinite μ]
    (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) (f : E → E → ℝ)
    (hf : Integrable (fun v : Fin 2 → E => f (v 0) (v 1)) (Measure.pi (fun _ => μ))) :
    Integrable (fun x : Fin (2*n) → E => pairingWeight (fun a b => f (x a) (x b)) M)
      (Measure.pi (fun _ => μ)) := by
  simp_rw [pairingWeight_comp_eq M hM]
  exact arbitrary_pairing_integrable n μ (matchingCoordinateEquiv M hM) (fun v => f (v 0) (v 1)) hf

theorem integrable_list_sum {ι X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : List ι) (F : ι → X → ℝ) (hF : ∀ i ∈ L, Integrable (F i) μ) :
    Integrable (fun x => (L.map (fun i => F i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hF i (by simp)).add (ih (fun j hj => hF j (by simp [hj])))

theorem integral_list_sum {ι X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : List ι) (F : ι → X → ℝ) (hF : ∀ i ∈ L, Integrable (F i) μ) :
    (∫ x, (L.map (fun i => F i x)).sum ∂μ) = (L.map (fun i => ∫ x, F i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hF i (by simp))
      (integrable_list_sum μ L F (fun j hj => hF j (by simp [hj])))]
    rw [ih (fun j hj => hF j (by simp [hj]))]

theorem list_sum_constant_real {ι : Type*} (L : List ι) (c : ℝ) :
    (L.map (fun _ => c)).sum=(L.length:ℝ)*c := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,ih]; ring

theorem pairingMajorant_integrable (n : ℕ) (μ : Measure E) [SigmaFinite μ] (f : E → E → ℝ)
    (hf : Integrable (fun v : Fin 2 → E => f (v 0) (v 1)) (Measure.pi (fun _ => μ))) :
    Integrable (fun x : Fin (2*n) → E =>
      pairingMajorant (fun a b => f (x a) (x b)) n (List.finRange (2*n)))
      (Measure.pi (fun _ => μ)) :=
  integrable_list_sum _ _ _ (fun M hM => pairingWeight_integrable μ M hM f hf)

theorem pairingMajorant_integral (n : ℕ) (μ : Measure E) [SigmaFinite μ] (f : E → E → ℝ)
    (hf : Integrable (fun v : Fin 2 → E => f (v 0) (v 1)) (Measure.pi (fun _ => μ))) :
    (∫ x : Fin (2*n) → E, pairingMajorant (fun a b => f (x a) (x b)) n (List.finRange (2*n))
      ∂Measure.pi (fun _ => μ)) =
      (matchingCount n:ℝ)*(∫ v : Fin 2 → E, f (v 0) (v 1) ∂Measure.pi (fun _ => μ))^n := by
  unfold pairingMajorant
  rw [integral_list_sum _ _ _ (fun M hM => pairingWeight_integrable μ M hM f hf)]
  have he : ((perfectPairings n (List.finRange (2*n))).map (fun M =>
      ∫ x : Fin (2*n) → E, pairingWeight (fun a b => f (x a) (x b)) M ∂Measure.pi (fun _ => μ))) =
      (perfectPairings n (List.finRange (2*n))).map (fun _ =>
        (∫ v : Fin 2 → E, f (v 0) (v 1) ∂Measure.pi (fun _ => μ))^n) := by
    apply List.map_congr_left
    exact fun M hM => pairingWeight_integral μ M hM f
  rw [he,list_sum_constant_real,perfectPairings_card n _ (by simp)]

theorem integral_norm_labelPfaffian_le (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (A : E → E → ℂ)
    (hpair : Integrable (fun v : Fin 2 → E => ‖A (v 0) (v 1)‖) (Measure.pi (fun _ => μ)))
    (hpf : AEStronglyMeasurable (fun x : Fin (2*n) → E =>
      labelPfaffian (fun a b => A (x a) (x b)) n (List.finRange (2*n)))
      (Measure.pi (fun _ => μ))) :
    (∫ x : Fin (2*n) → E, ‖labelPfaffian (fun a b => A (x a) (x b)) n (List.finRange (2*n))‖
      ∂Measure.pi (fun _ => μ)) ≤
      (matchingCount n:ℝ)*(∫ v : Fin 2 → E, ‖A (v 0) (v 1)‖ ∂Measure.pi (fun _ => μ))^n := by
  have hG := pairingMajorant_integrable n μ (fun x y => ‖A x y‖) hpair
  have hbound (x : Fin (2*n) → E) := labelPfaffian_norm_le_pairings
    (fun a b => A (x a) (x b)) (fun a b => ‖A (x a) (x b)‖)
    (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl) n (List.finRange (2*n))
  have hFi := hG.mono' hpf (Filter.Eventually.of_forall hbound)
  calc
    _ ≤ ∫ x : Fin (2*n) → E,
        pairingMajorant (fun a b => ‖A (x a) (x b)‖) n (List.finRange (2*n))
        ∂Measure.pi (fun _ => μ) := integral_mono hFi.norm hG hbound
    _ = _ := pairingMajorant_integral n μ (fun x y => ‖A x y‖) hpair

end
end IsingBulk.Tail
