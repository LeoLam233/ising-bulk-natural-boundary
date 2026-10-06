import IsingBulk.Tail.WeightedPairingIntegral
import IsingBulk.Tail.UltraHighPairEstimate

namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set IsingBulk.First
open scoped Topology

theorem continuous_labelPfaffian {X α : Type*} [TopologicalSpace X]
    (A : X → α → α → ℂ) (hA : ∀ a b, Continuous (fun x => A x a b))
    (n : ℕ) (xs : List α) : Continuous (fun x => labelPfaffian (A x) n xs) := by
  induction n generalizing xs with
  | zero => exact continuous_const
  | succ n ih =>
    cases xs with
    | nil => exact continuous_const
    | cons a xs =>
      change Continuous (fun x => (xs.zipIdx.map (fun bj =>
        (-1:ℂ)^bj.2*A x a bj.1*labelPfaffian (A x) n (xs.eraseIdx bj.2))).sum)
      apply continuous_list_sum
      intro bj hbj
      exact (continuous_const.mul (hA a bj.1)).mul (ih _)

theorem continuous_list_prod_map {X α : Type*} [TopologicalSpace X]
    (c : X → α → ℝ) (hc : ∀ a, Continuous (fun x => c x a)) (xs : List α) :
    Continuous (fun x => (xs.map (c x)).prod) := by
  induction xs with
  | nil => exact continuous_const
  | cons a xs ih => exact (hc a).mul ih

theorem pair_pi_integral_eq_prod (T : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ v : Fin 2 → ℝ, f (v 0) (v 1)
      ∂Measure.pi (fun _ => volume.restrict (Icc 0 T))) =
      ∫ p in Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T, f p.1 p.2 := by
  rw [← (measurePreserving_piFinTwo
    (fun _ : Fin 2 => volume.restrict (Icc (0:ℝ) T))).symm.integral_comp']
  simp only [MeasurableEquiv.piFinTwo_symm_apply]
  rw [Measure.prod_restrict]
  rfl

theorem pair_pi_integrable (T : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Integrable (fun v : Fin 2 → ℝ => f (v 0) (v 1))
      (Measure.pi (fun _ => volume.restrict (Icc 0 T))) := by
  rw [← (measurePreserving_piFinTwo
    (fun _ : Fin 2 => volume.restrict (Icc (0:ℝ) T))).symm.integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
  simp only [Function.comp_def,MeasurableEquiv.piFinTwo_symm_apply]
  rw [Measure.prod_restrict]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem weighted_angular_pfaffian_integral (n : ℕ) (T : ℝ)
    (c : ℝ → ℝ) (hc : Continuous c) (hcpos : ∀ x, 0 ≤ c x)
    (A : ℝ → ℝ → ℂ) (hA : Continuous (Function.uncurry A)) :
    (∫ x : Fin (2*n) → ℝ,
      ((List.finRange (2*n)).map (fun a => c (x a))).prod *
      ‖labelPfaffian (fun a b => A (x a) (x b)) n (List.finRange (2*n))‖
      ∂Measure.pi (fun _ => volume.restrict (Icc 0 T))) ≤
      (matchingCount n:ℝ)*(∫ p in Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T,
        c p.1*c p.2*‖A p.1 p.2‖)^n := by
  have hpair : Continuous (fun p : ℝ × ℝ => c p.1*c p.2*‖A p.1 p.2‖) :=
    ((hc.comp continuous_fst).mul (hc.comp continuous_snd)).mul hA.norm
  have hp := integral_weighted_labelPfaffian_le n (volume.restrict (Icc (0:ℝ) T))
    c hcpos A (pair_pi_integrable T (fun x y => c x*c y*‖A x y‖) hpair) ?_
  · rw [pair_pi_integral_eq_prod T (fun x y => c x*c y*‖A x y‖)] at hp
    exact hp
  · apply Continuous.aestronglyMeasurable
    apply (continuous_list_prod_map (fun (x : Fin (2*n) → ℝ) a => c (x a))
      (fun a => hc.comp (continuous_apply a)) _).mul
    apply Continuous.norm
    apply continuous_labelPfaffian (fun (x : Fin (2*n) → ℝ) a b => A (x a) (x b))
    intro a b
    exact hA.comp (show Continuous (fun x : Fin (2*n) → ℝ => (x a,x b)) from
      (continuous_apply a).prodMk (continuous_apply b))

end
end IsingBulk.Tail
