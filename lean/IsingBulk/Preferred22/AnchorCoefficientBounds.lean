import IsingBulk.Preferred22.AnchorTransportIteration
import IsingBulk.Preferred22.AnchorCutoffFrameJets

/-! Quantitative induction for the literal anchored scalar recurrence.
The induction uses only actual finite frame jets of its original seed and
residual field; it never assumes estimates for generated descendants. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem preferredCellRegularTransportStep_mixed {N : ℕ}
    (cell : PreferredTransportCell N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ i,PreferredMixedSmoothOn
      (fun z => preferredResidualField cell z.1 (preferredSourceCoordinate τ p m z.1 z.2) i) Ω)
    (G : ℂ → (Fin N → ℝ) → ℂ) (hG : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω) :
    PreferredMixedSmoothOn (fun z => preferredCellRegularTransportStep cell τ p m G z.1 z.2) Ω := by
  have hGs := preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint none G hG
  have hGq (a : Fin N) := preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some a) G hG
  have hBq (a : Fin N) := preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some a)
    (fun t x => preferredResidualField cell t (preferredSourceCoordinate τ p m t x) a) (hB a)
  exact (hGs.add (PreferredMixedSmoothOn.sum (fun a => (hB a).mul (hGq a)))).add
    ((PreferredMixedSmoothOn.sum hBq).mul hG)

theorem preferredCellRegularScalar_mixed_of_base {N : ℕ}
    (cell : PreferredTransportCell N) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2)
    (hB : ∀ i,PreferredMixedSmoothOn
      (fun z => preferredResidualField cell z.1 (preferredSourceCoordinate τ p m z.1 z.2) i) Ω)
    (hA : PreferredMixedSmoothOn (fun z => preferredCellRegularSeed cell τ η p m r z.1 z.2) Ω) :
    ∀ j,PreferredMixedSmoothOn (fun z => preferredCellRegularScalar cell τ η p m r j z.1 z.2) Ω := by
  intro j
  induction j with
  | zero => exact hA
  | succ j ih => exact preferredCellRegularTransportStep_mixed cell τ δ p m hp hm Ω hΩ hpoint hB _ ih

/-- One genuine scalar transport step has a finite frame bound with two
N-term sums and the exact real-cutoff Leibniz expansion. -/
theorem preferredCellRegularTransportStep_frame_bound {N : ℕ}
    (cell : PreferredTransportCell N) (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2)
    (hBm : ∀ i,PreferredMixedSmoothOn
      (fun z => preferredResidualField cell z.1 (preferredSourceCoordinate τ p m z.1 z.2) i) Ω)
    (G : ℂ → (Fin N → ℝ) → ℂ) (hGm : PreferredMixedSmoothOn (fun z => G z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (K : ℕ) (M X : ℝ) (hM : 0≤M) (hX : 0≤X)
    (hB : ∀ i,∀ ys : List (Option (Fin N)),ys.length≤K+1 →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualField cell t (preferredSourceCoordinate τ p m t x) i) ys s θ‖≤M)
    (hG : ∀ ys : List (Option (Fin N)),ys.length≤K+1 → ‖preferredFrameJet τ p m G ys s θ‖≤X)
    (xs : List (Option (Fin N))) (hxs : xs.length≤K) :
    ‖preferredFrameJet τ p m (preferredCellRegularTransportStep cell τ p m G) xs s θ‖≤
      (1+2^(K+1)*(N:ℝ)*M)*X := by
  let B := fun i t x => preferredResidualField cell t (preferredSourceCoordinate τ p m t x) i
  let D := fun t x => ∑ i : Fin N,preferredCoordinateFrame τ p m i (B i) t x
  let F₀ := preferredParameterFrame τ p m G
  let F₁ := fun t x => ∑ i : Fin N,B i t x*preferredCoordinateFrame τ p m i G t x
  let F₂ := fun t x => D t x*G t x
  have hGq (i : Fin N) : PreferredMixedSmoothOn (fun z => preferredCoordinateFrame τ p m i G z.1 z.2) Ω :=
    preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some i) G hGm
  have hBq (i : Fin N) : PreferredMixedSmoothOn (fun z => preferredCoordinateFrame τ p m i (B i) z.1 z.2) Ω :=
    preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint (some i) (B i) (hBm i)
  have hDm : PreferredMixedSmoothOn (fun z => D z.1 z.2) Ω := PreferredMixedSmoothOn.sum hBq
  have hF₀ : PreferredMixedSmoothOn (fun z => F₀ z.1 z.2) Ω :=
    preferredFrameStep_mixed τ δ p m hp hm Ω hΩ hpoint none G hGm
  have hF₁ : PreferredMixedSmoothOn (fun z => F₁ z.1 z.2) Ω :=
    PreferredMixedSmoothOn.sum (fun i => (hBm i).mul (hGq i))
  have hF₂ : PreferredMixedSmoothOn (fun z => F₂ z.1 z.2) Ω := hDm.mul hGm
  have hstep (a : Option (Fin N)) (ys : List (Option (Fin N))) (hys : ys.length≤K) :
      ‖preferredFrameJet τ p m (preferredFrameStep τ p m a G) ys s θ‖≤X := by
    have he : preferredFrameStep τ p m a G=preferredFrameJet τ p m G [a] := by cases a <;> rfl
    rw [he,preferredFrameJet_append]
    exact hG (ys++[a]) (by simpa only [List.length_append,List.length_singleton] using Nat.add_le_add_right hys 1)
  have hD (ys : List (Option (Fin N))) (hys : ys.length≤K) :
      ‖preferredFrameJet τ p m D ys s θ‖≤(N:ℝ)*M := by
    rw [preferredFrameJet_sum τ δ p m hp hm Ω hΩ hpoint _ hBq ys s θ hz]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin N,M := by
        apply Finset.sum_le_sum
        intro i _
        change ‖preferredFrameJet τ p m (preferredFrameJet τ p m (B i) [some i]) ys s θ‖≤M
        rw [preferredFrameJet_append]
        exact hB i (ys++[some i]) (by simpa only [List.length_append,List.length_singleton] using Nat.add_le_add_right hys 1)
      _ = _ := by simp
  have hF₁b : ‖preferredFrameJet τ p m F₁ xs s θ‖≤(N:ℝ)*(2^K*M*X) := by
    rw [preferredFrameJet_sum τ δ p m hp hm Ω hΩ hpoint _ (fun i => (hBm i).mul (hGq i)) xs s θ hz]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin N,2^K*M*X := by
        apply Finset.sum_le_sum
        intro i _
        exact preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint (B i)
          (preferredCoordinateFrame τ p m i G) (hBm i) (hGq i) s θ hz K M X hM hX
          (fun ys hys => hB i ys (hys.trans (Nat.le_succ _))) (hstep (some i)) xs hxs
      _ = _ := by simp
  have hF₂b : ‖preferredFrameJet τ p m F₂ xs s θ‖≤2^K*((N:ℝ)*M)*X :=
    preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hpoint D G hDm hGm s θ hz K
      ((N:ℝ)*M) X (by positivity) hX hD (fun ys hys => hG ys (hys.trans (Nat.le_succ _))) xs hxs
  change ‖preferredFrameJet τ p m (fun t x => F₀ t x+F₁ t x+F₂ t x) xs s θ‖≤_
  rw [preferredFrameJet_add τ δ p m hp hm Ω hΩ hpoint _ F₂ (hF₀.add hF₁) hF₂ xs s θ hz,
    preferredFrameJet_add τ δ p m hp hm Ω hΩ hpoint F₀ F₁ hF₀ hF₁ xs s θ hz]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  calc
    _ ≤ X+(N:ℝ)*(2^K*M*X)+2^K*((N:ℝ)*M)*X :=
      add_le_add (add_le_add (hstep none xs hxs) hF₁b) hF₂b
    _ = _ := by rw [pow_succ]; ring

/-- Every generated scalar coefficient follows from the finite seed/field
jet inputs, with polynomial particle cost and no collision loss. -/
theorem preferredCellRegularScalar_frame_bound {N : ℕ}
    (cell : PreferredTransportCell N) (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω,PreferredFramePoint τ δ p m z.1 z.2)
    (hBm : ∀ i,PreferredMixedSmoothOn
      (fun z => preferredResidualField cell z.1 (preferredSourceCoordinate τ p m z.1 z.2) i) Ω)
    (hAm : PreferredMixedSmoothOn (fun z => preferredCellRegularSeed cell τ η p m r z.1 z.2) Ω)
    (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) (J : ℕ) (M A : ℝ) (hM : 0≤M) (hA : 0≤A)
    (hB : ∀ i,∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m
        (fun t x => preferredResidualField cell t (preferredSourceCoordinate τ p m t x) i) ys s θ‖≤M)
    (hSeed : ∀ ys : List (Option (Fin N)),ys.length≤J →
      ‖preferredFrameJet τ p m (preferredCellRegularSeed cell τ η p m r) ys s θ‖≤A) :
    ∀ j≤J,∀ xs : List (Option (Fin N)),xs.length+j≤J →
      ‖preferredFrameJet τ p m (preferredCellRegularScalar cell τ η p m r j) xs s θ‖≤
        (1+2^(J+1)*(N:ℝ)*M)^j*A := by
  have hmix := preferredCellRegularScalar_mixed_of_base cell τ δ η p m r hp hm Ω hΩ hpoint hBm hAm
  let C := 1+2^(J+1)*(N:ℝ)*M
  have hC : 0≤C := by dsimp [C]; positivity
  intro j
  induction j with
  | zero =>
    intro _ xs hxs
    simpa only [preferredCellRegularScalar,pow_zero,one_mul,Nat.add_zero] using hSeed xs hxs
  | succ j ih =>
    intro hj xs hxs
    let K := J-(j+1)
    have hK : K+1≤J := by dsimp [K]; omega
    have hxsK : xs.length≤K := by dsimp [K]; omega
    have hGj (ys : List (Option (Fin N))) (hys : ys.length≤K+1) :
        ‖preferredFrameJet τ p m (preferredCellRegularScalar cell τ η p m r j) ys s θ‖≤C^j*A :=
      ih (by omega) ys (by dsimp [K] at hys; omega)
    have hh := preferredCellRegularTransportStep_frame_bound cell τ δ p m hp hm Ω hΩ hpoint hBm
      (preferredCellRegularScalar cell τ η p m r j) (hmix j) s θ hz K M (C^j*A) hM (by positivity)
      (fun i ys hys => hB i ys (hys.trans hK)) hGj xs hxsK
    change ‖preferredFrameJet τ p m
      (preferredCellRegularTransportStep cell τ p m (preferredCellRegularScalar cell τ η p m r j)) xs s θ‖≤_
    apply hh.trans
    have hc : 1+2^(K+1)*(N:ℝ)*M≤C := by
      dsimp [C]
      simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
          (by omega : K+1≤J+1)) (Nat.cast_nonneg N)) hM) 1
    calc
      _ ≤ C*(C^j*A) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = C^(j+1)*A := by rw [pow_succ]; ring

end
end IsingBulk.Preferred22
