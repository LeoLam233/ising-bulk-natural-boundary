import IsingBulk.Preferred22.VandermondeTransport
import IsingBulk.Preferred22.ShellGeometry
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Cast

/-! The complete squared-Vandermonde degree, and its actual finite-mean
shell scale. No partial-collision factor is discarded. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators

/-- The upper-pair representation is exactly a product over all strict
ordered labels, so its degree is N(N-1). -/
theorem preferredSquaredVandermonde_pairProduct {N : ℕ} (q : Fin N → ℂ) :
    preferredSquaredVandermonde q=
      ∏ p∈(Finset.univ.filter (fun p : Fin N × Fin N => p.1<p.2)),(q p.1-q p.2)^2 := by
  classical
  have hi (i : Fin N) : Finset.Ioi i=Finset.univ.filter (fun a : Fin N => i<a) := by
    ext a
    simp
  unfold preferredSquaredVandermonde
  simp_rw [hi,Finset.prod_filter]
  rw [←Finset.univ_product_univ,Finset.prod_product]

/-- Genuine full degree with the actual complex source differences. -/
theorem preferredSquaredVandermonde_norm_le {N : ℕ} (q : Fin N → ℂ)
    {A : ℝ} (hq : ∀ i j,‖q i-q j‖≤A) :
    ‖preferredSquaredVandermonde q‖≤A^(N*(N-1)) := by
  classical
  let S := Finset.univ.filter (fun p : Fin N × Fin N => p.1<p.2)
  have hcard : S.card=N.choose 2 := by
    simpa only [S,Fintype.card_fin] using (Fintype.card_product_filter_lt (α := Fin N))
  have hdegree : 2*S.card=N*(N-1) := by
    rw [hcard]
    have h := Nat.descFactorial_eq_factorial_mul_choose N 2
    norm_num [Nat.descFactorial_succ] at h
    simpa only [mul_comm] using h.symm
  rw [preferredSquaredVandermonde_pairProduct,norm_prod]
  calc
    _ ≤ ∏ _p∈S,A^2 := Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hq p.1 p.2) 2)
    _ = A^(N*(N-1)) := by rw [Finset.prod_const,←pow_mul,hdegree]

/-- The exact q23 endpoint estimate gives the complete finite-particle
Vandermonde power whenever the true constrained mean has a positive gap. -/
theorem preferred_actual_finite_vandermonde_scale (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ C ε₀ τ₀ δ₀ : ℝ,0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δ₀ ∧ δ₀<B.delta ∧
      ∀ δB ε τ r g : ℝ,δB≤δ₀ → 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → 0<g →
      ∀ n : ℕ,∀ l : ℤ,g≤|preferredShellMean d (n+1) l| → ∀ i a : Fin (n+1),
      ∀ x∈preferredRightShell d B δB r l i a,
      ‖preferredSquaredVandermonde (preferredSourceCoordinate τ B.p B.m
        (IsingBulk.Branch.radialParameter d.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAngles x)))‖≤
        (C/Real.sqrt g)^((n+1)*n)*r^((n+1)*n) := by
  obtain ⟨C,ε₀,τ₀,δ₀,hC,hε₀,hτ₀,hδ₀,hδ₀δ,hdiff⟩ := preferred_actual_coordinate_difference d B
  refine ⟨C,ε₀,τ₀,δ₀,hC,hε₀,hτ₀,hδ₀,hδ₀δ,?_⟩
  intro δB ε τ r g hδB hε hεr hτ hτr hr hg n l hmean i a x hx
  let θ := preferredLiftedAngles B.delta (constrainedAngles x)
  let T := preferredShellScale d (n+1) l r ε
  have hgT : g≤T := by dsimp [T,preferredShellScale]; linarith
  have hgq : 0<Real.sqrt g := Real.sqrt_pos.mpr hg
  have hqT : Real.sqrt g≤Real.sqrt T := Real.sqrt_le_sqrt hgT
  have hd := hdiff (n+1) (by omega) ε τ (preferredShellMean d (n+1) l) r hε hεr hτ hτr hr θ
    (fun v => ⟨by linarith [(hx.2.1 v).1],by linarith [(hx.2.1 v).2]⟩)
    (preferredRightShell_window d B hx)
  have hp := preferredSquaredVandermonde_norm_le
    (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ)
    (fun u v =>
      (hd u v).trans (div_le_div_of_nonneg_left (by positivity) hgq hqT))
  simpa only [Nat.add_sub_cancel,mul_div_right_comm,mul_pow] using hp

end
end IsingBulk.Preferred22
