import IsingBulk.HT22.Tail.SignedRadialIntegralRecurrence
import IsingBulk.Preferred22.RadialDerivativeLimit

/-! Unpuncturing uses local uniform convergence of the derivatives, not a
pointwise-limit shortcut. Only the published density-independent compact
uniform derivative-limit theorem is reused. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_of_puncture_log_errors
    (P Q J : ℕ → ℝ → ℂ) (I I' : ℝ → ℂ) (ζ : ℂ) (hζ : ‖ζ‖=1)
    {ε₀ ρ A B C : ℝ} (hρ : 0≤ρ) (hρ1 : ρ<1)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (hderiv : ∀ m ε,ε∈Ioo 0 ε₀ → HasDerivAt (P m) (ζ*(Q m ε-J m ε)) ε)
    (hvalue : ∀ m ε,ε∈Ioo 0 ε₀ → ‖P m ε-I ε‖≤A*(1+|Real.log ε|)*ρ^m)
    (hnext : ∀ m ε,ε∈Ioo 0 ε₀ → ‖Q m ε-I' ε‖≤B*(1+|Real.log ε|)*ρ^m)
    (hflux : ∀ m ε,ε∈Ioo 0 ε₀ → ‖J m ε‖≤C*(1+|Real.log ε|)*ρ^m)
    {ε : ℝ} (hε : ε∈Ioo 0 ε₀) : HasDerivAt I (ζ*I' ε) ε := by
  apply preferred_hasDerivAt_of_log_geometric_approximants P
    (fun m t => ζ*(Q m t-J m t)) I (fun t => ζ*I' t)
    hρ hρ1 hA (add_nonneg hB hC) hderiv hvalue (ε:=ε) ?_ hε
  intro m t ht
  have he : ζ*(Q m t-J m t)-ζ*I' t=ζ*((Q m t-I' t)-J m t) := by ring
  rw [he,norm_mul,hζ,one_mul]
  calc
    _ ≤ ‖Q m t-I' t‖+‖J m t‖ := norm_sub_le _ _
    _ ≤ B*(1+|Real.log t|)*ρ^m+C*(1+|Real.log t|)*ρ^m :=
      add_le_add (hnext m t ht) (hflux m t ht)
    _ = _ := by ring

/-- Repeated complex derivatives follow from the proved radial derivative
identities and analyticity of the original zeroth observable. -/
theorem iteratedDeriv_eq_of_radial_derivatives (α ε₀ : ℝ) (I : ℕ → ℂ → ℂ) (k : ℕ)
    (hI : ∀ ε∈Ioo 0 ε₀,AnalyticAt ℂ (I 0) (IsingBulk.Branch.radialParameter α ε))
    (hderiv : ∀ j : ℕ,j<k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      HasDerivAt (fun u => I j (IsingBulk.Branch.radialParameter α u))
        (Complex.exp ((α:ℂ)*Complex.I)*I (j+1) (IsingBulk.Branch.radialParameter α ε)) ε) :
    ∀ j : ℕ,j≤k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      iteratedDeriv j (I 0) (IsingBulk.Branch.radialParameter α ε)=
        I j (IsingBulk.Branch.radialParameter α ε) := by
  intro j
  induction j with
  | zero => intro _ ε _; rfl
  | succ j ih =>
    intro hj ε hε
    have he : (fun u : ℝ => iteratedDeriv j (I 0) (IsingBulk.Branch.radialParameter α u))
        =ᶠ[𝓝 ε] (fun u => I j (IsingBulk.Branch.radialParameter α u)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hε] with u hu
      exact ih (by omega) u hu
    have hf := radial_point_hasDerivAt α ε (iteratedDeriv j (I 0))
      (IsingBulk.First.analyticAt_iteratedDeriv (hI ε hε) j).differentiableAt
    have hg := hderiv j (by omega) ε hε
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((α:ℂ)*Complex.I))
    have hh := hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)
    simpa only [iteratedDeriv_succ] using hh

/-- The same radial uniqueness argument with a separately named original
physical germ, so zeroth integral identity need hold only on the radial path. -/
theorem physical_iteratedDeriv_eq_of_radial_derivatives (α ε₀ : ℝ)
    (F : ℂ → ℂ) (I : ℕ → ℂ → ℂ) (k : ℕ)
    (hF : ∀ ε∈Ioo 0 ε₀,AnalyticAt ℂ F (IsingBulk.Branch.radialParameter α ε))
    (hzero : ∀ ε∈Ioo 0 ε₀,F (IsingBulk.Branch.radialParameter α ε)=I 0 (IsingBulk.Branch.radialParameter α ε))
    (hderiv : ∀ j : ℕ,j<k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      HasDerivAt (fun u => I j (IsingBulk.Branch.radialParameter α u))
        (Complex.exp ((α:ℂ)*Complex.I)*I (j+1) (IsingBulk.Branch.radialParameter α ε)) ε) :
    ∀ j : ℕ,j≤k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      iteratedDeriv j F (IsingBulk.Branch.radialParameter α ε)=
        I j (IsingBulk.Branch.radialParameter α ε) := by
  intro j
  induction j with
  | zero => intro _ ε hε;exact hzero ε hε
  | succ j ih =>
    intro hj ε hε
    have he : (fun u : ℝ => iteratedDeriv j F (IsingBulk.Branch.radialParameter α u))
        =ᶠ[𝓝 ε] (fun u => I j (IsingBulk.Branch.radialParameter α u)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hε] with u hu
      exact ih (by omega) u hu
    have hf := radial_point_hasDerivAt α ε (iteratedDeriv j F)
      (IsingBulk.First.analyticAt_iteratedDeriv (hF ε hε) j).differentiableAt
    have hg := hderiv j (by omega) ε hε
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((α:ℂ)*Complex.I))
    have hh := hf.deriv.symm.trans (he.deriv_eq.trans hg.deriv)
    simpa only [iteratedDeriv_succ] using hh

/-- A fixed-order family of actual punctured radial identities and genuine
geometric value/flux errors gives the full repeated derivative identity. -/
theorem iteratedDeriv_eq_of_puncture_log_errors (α ε₀ : ℝ)
    (I : ℕ → ℂ → ℂ) (P J : ℕ → ℕ → ℝ → ℂ) (k : ℕ)
    (hI : ∀ ε∈Ioo 0 ε₀,AnalyticAt ℂ (I 0) (IsingBulk.Branch.radialParameter α ε))
    {ρ : ℝ} (hρ : 0≤ρ) (hρ1 : ρ<1)
    (hderiv : ∀ j : ℕ,j<k → ∀ m ε,ε∈Ioo 0 ε₀ →
      HasDerivAt (P j m) (Complex.exp ((α:ℂ)*Complex.I)*(P (j+1) m ε-J j m ε)) ε)
    (hvalue : ∀ j : ℕ,j≤k → ∃ A : ℝ,0≤A ∧ ∀ m ε,ε∈Ioo 0 ε₀ →
      ‖P j m ε-I j (IsingBulk.Branch.radialParameter α ε)‖≤A*(1+|Real.log ε|)*ρ^m)
    (hflux : ∀ j : ℕ,j<k → ∃ C : ℝ,0≤C ∧ ∀ m ε,ε∈Ioo 0 ε₀ →
      ‖J j m ε‖≤C*(1+|Real.log ε|)*ρ^m) :
    ∀ j : ℕ,j≤k → ∀ ε : ℝ,ε∈Ioo 0 ε₀ →
      iteratedDeriv j (I 0) (IsingBulk.Branch.radialParameter α ε)=
        I j (IsingBulk.Branch.radialParameter α ε) := by
  apply iteratedDeriv_eq_of_radial_derivatives α ε₀ I k hI
  intro j hj ε hε
  obtain ⟨A,hA,hv⟩ := hvalue j (by omega)
  obtain ⟨B,hB,hn⟩ := hvalue (j+1) (by omega)
  obtain ⟨C,hC,hf⟩ := hflux j hj
  exact hasDerivAt_of_puncture_log_errors (P j) (P (j+1)) (J j)
    (fun u => I j (IsingBulk.Branch.radialParameter α u))
    (fun u => I (j+1) (IsingBulk.Branch.radialParameter α u))
    (Complex.exp ((α:ℂ)*Complex.I)) (Complex.norm_exp_ofReal_mul_I α)
    hρ hρ1 hA hB hC (hderiv j hj) hv hn hf hε

end
end IsingBulk.HT22.Tail
