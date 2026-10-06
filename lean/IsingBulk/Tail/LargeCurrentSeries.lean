import IsingBulk.Tail.LargeCurrentTheorem

/-! Absolute summation of the actual differentiated large-lambda current
at every positive even order, stronger than the manuscript's finite window. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000

theorem large_current_positive_even_series (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ, 0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,
        0<α → α<α₀ → 0<τ → τ<τ₀ →
        ∃ eps₀ : ℝ, 0<eps₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0<C ∧
          ∀ eps lamStar : ℝ, 0<eps → eps<eps₀ → 0<lamStar → lamStar≤1 →
            Summable (fun n : ℕ => ‖∫ lam in lamStar..1,
              differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB η α)
                (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)‖) ∧
            (∑' n : ℕ, ‖∫ lam in lamStar..1,
              differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB η α)
                (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)‖)≤C*(lamStar⁻¹)^(j+1) := by
  obtain ⟨η₀,hη₀,hsetup⟩ := large_current_per_order d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hnext⟩ := hsetup η hη hηlt
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  obtain ⟨c,e,K,D,κ,hc,he,hK,hD,hκ,hbound⟩ := hnext α τ hα hαlt hτ hτlt
  refine ⟨e,he,?_⟩
  intro j
  let A := (j.factorial:ℝ)*K/c^j
  let g : ℕ → ℝ := fun n => D^(2*(n+1))*((2*(n+1):ℕ):ℝ)^(2*j)*Real.exp (-κ*((2*(n+1):ℕ):ℝ)^2)
  have hA : 0<A := by dsimp [A]; positivity
  have hg0 : ∀ n, 0≤g n := by intro n; dsimp [g]; positivity
  have hg : Summable g := (summable_source_gaussian hD.le hκ (2*j)).comp_injective
    (show Function.Injective (fun n : ℕ => 2*(n+1)) by intro a b hab; dsimp at hab; omega)
  let C := A*((∑' n, g n)+1)
  have hC : 0<C := by dsimp [C]; have hh : 0≤∑' n, g n := tsum_nonneg hg0; positivity
  refine ⟨C,hC,?_⟩
  intro eps lamStar heps hepslt hls hls1
  let L := (lamStar⁻¹)^(j+1)
  have hL : 0≤L := by dsimp [L]; positivity
  have hpoint (n : ℕ) :
      ‖∫ lam in lamStar..1, differentiatedCurrentSlice (2*(n+1)) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)‖≤(A*L)*g n := by
    have hh := (hbound (2*(n+1)) j eps lamStar (by omega) heps hepslt hls hls1).2
    convert hh using 1
    dsimp [A,L,g]
    ring
  have hdom := hg.mul_left (A*L)
  have hsum := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hdom
  refine ⟨hsum,?_⟩
  have hh := Summable.tsum_le_tsum hpoint hsum hdom
  rw [tsum_mul_left] at hh
  apply hh.trans
  dsimp only [C,L]
  nlinarith [mul_nonneg hA.le hL]

end
end IsingBulk.Tail
