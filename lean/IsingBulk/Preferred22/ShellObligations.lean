import IsingBulk.Preferred22.Transport
import IsingBulk.Preferred22.BumpExistence
import IsingBulk.Preferred22.AbsoluteTail

/-!
# Exact remaining shell obligations

These propositions concern the literal transported physical density. They are
not axioms and are not used to claim the actual higher tail has been proved.
-/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory

/-- The actual population partition can be chosen explicitly. -/
def preferredPopulationCutoff (t : ℝ) : ℝ := Real.smoothTransition (4*t-1)

theorem preferredPopulationCutoff_smooth : ContDiff ℝ ∞ preferredPopulationCutoff := by
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem preferredPopulationCutoff_bounds (t : ℝ) :
    0 ≤ preferredPopulationCutoff t ∧ preferredPopulationCutoff t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem preferredPopulationCutoff_zero {t : ℝ} (ht : t ≤ 1/4) :
    preferredPopulationCutoff t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

theorem preferredPopulationCutoff_one {t : ℝ} (ht : 1/2 ≤ t) :
    preferredPopulationCutoff t = 1 := Real.smoothTransition.one_of_one_le (by linarith)

/-- Precise remaining smooth right-cutoff data on the actual one-sided
angular lift. Its periodic return lies in the excluded upper plateau. -/
def PreferredRightCutoffData (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB : ℝ) (r : ℝ → ℝ) : Prop :=
  0 < δB ∧ δB < B.delta ∧ ContDiff ℝ ∞ r ∧ Function.Periodic r (2*Real.pi) ∧
    (∀ θ, 0 ≤ r θ ∧ r θ ≤ 1) ∧
    (∀ θ ∈ Icc (-Real.pi-B.delta) B.delta,
      (θ+d.b ≤ -δB → r θ = 0) ∧ (-δB/2 ≤ θ+d.b → r θ = 1))

/-- The shell is cut only in the final real absolute integral, after all
transport. Both actual extrema, one constrained mean, and the entire right
rectangle are retained. No derivatives of extrema or shell scales occur. -/
def preferredRightShell {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB r : ℝ) (l : ℤ) (i j : Fin (n+1)) : Set (Fin n → ℝ) :=
  {θ | θ ∈ angularBox n ∧
    let w := preferredLiftedAngles B.delta (constrainedAngles θ)
    (∀ v, w v ∈ Icc (-d.b-δB) B.delta) ∧
    (∑ v, w v) = 2*Real.pi*(l:ℝ) ∧
    (∀ v, w i ≤ w v ∧ w v ≤ w j) ∧ r ≤ w j-w i ∧ w j-w i ≤ 2*r}

def preferredShellMean (d : PreferredBranchData) (N : ℕ) (l : ℤ) : ℝ :=
  d.b+2*Real.pi*(l:ℝ)/(N:ℝ)

def preferredShellScale (d : PreferredBranchData) (N : ℕ) (l : ℤ) (r ε : ℝ) : ℝ :=
  |preferredShellMean d N l|+r+ε

/-- The actual q28 left hand side, including the complete normalization,
physical root, coupled contour Jacobian, cutoffs and all transported jets. -/
def preferredRightShellMass {n : ℕ} (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB τ : ℝ) (η rcut : ℝ → ℝ) (j : ℕ) (ε r : ℝ) (l : ℤ) (i a : Fin (n+1)) : ℝ :=
  ∫ θ in preferredRightShell d B δB r l i a,
    ‖preferredTransportedDensity .right τ η B.p B.m rcut j
      (IsingBulk.Branch.radialParameter d.alpha ε)
      (preferredLiftedAngles B.delta (constrainedAngles θ))‖

/-- Exact unproved all-diameter shell estimate (q28), including genuine
integrability. Its constants precede the particle order, actual mean, extrema,
epsilon and every positive diameter. -/
def PreferredAllDiameterShellBound (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB τ ε₀ : ℝ) (η rcut : ℝ → ℝ) (k : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ k → ∃ C : ℝ, ∃ J : ℕ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n+1 → Even (n+1) → ∀ ε r : ℝ,
    0 < ε → ε < ε₀ → 0 < r → ∀ l : ℤ, ∀ i a : Fin (n+1),
      IntegrableOn (fun θ =>
        ‖preferredTransportedDensity .right τ η B.p B.m rcut j
          (IsingBulk.Branch.radialParameter d.alpha ε)
          (preferredLiftedAngles B.delta (constrainedAngles θ))‖)
        (preferredRightShell d B δB r l i a) ∧
      preferredRightShellMass d B δB τ η rcut j ε r l i a ≤
        C^(n+1)*((n+1:ℕ):ℝ)^(-((n+1:ℕ):ℝ)/2+(J:ℝ)) *
        r^(2*((n+1:ℕ):ℝ)-2*(j:ℝ)-3) *
        (preferredShellScale d (n+1) l r ε)^(-((n+1:ℕ):ℝ)+3/2) *
        (1+|Real.log ε|)

/-- The distinct finite-block obligation uses the full Vandermonde degree
at sufficiently small diameters after the finite constrained-mean gap choice. -/
def PreferredFiniteBlockShellBound (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (δB τ ε₀ : ℝ) (η rcut : ℝ → ℝ) (Nstar k : ℕ) : Prop :=
  ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ n : ℕ,
    Nstar+2 ≤ n+1 → n+1 ≤ 2*k+4 → Even (n+1) → ∀ j : ℕ, j ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∀ ε r : ℝ, 0 < ε → ε < ε₀ → 0 < r → r < r₀ →
    ∀ l : ℤ, ∀ i a : Fin (n+1),
      preferredRightShellMass d B δB τ η rcut j ε r l i a ≤
        C*r^(((n+1:ℕ):ℝ)^2-2*(j:ℝ)-3)*(1+|Real.log ε|)

/-- The fixed-mean geometry used by all shell estimates is elementary and
holds for the actual constrained angular cell. -/
theorem constrained_shell_coordinate_window {N : ℕ} (hN : 0 < N)
    {u : Fin N → ℝ} {i j : Fin N} {t r : ℝ}
    (hmean : (∑ v, u v) = (N:ℝ)*t)
    (hext : ∀ v, u i ≤ u v ∧ u v ≤ u j) (hdiam : u j-u i ≤ 2*r) :
    ∀ v, t-2*r ≤ u v ∧ u v ≤ t+2*r := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  have hmin : (N:ℝ)*u i ≤ (N:ℝ)*t := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => (hext v).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hmean] using h
  have hmax : (N:ℝ)*t ≤ (N:ℝ)*u j := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => (hext v).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hmean] using h
  have hmi : u i ≤ t := le_of_mul_le_mul_left hmin hNp
  have hma : t ≤ u j := le_of_mul_le_mul_left hmax hNp
  intro v
  constructor <;> linarith [(hext v).1,(hext v).2]

theorem preferredShellScale_ge_diameter (d : PreferredBranchData) (N : ℕ) (l : ℤ)
    (r : ℝ) {ε : ℝ} (hε : 0 ≤ ε) : r ≤ preferredShellScale d N l r ε := by
  unfold preferredShellScale
  linarith [abs_nonneg (preferredShellMean d N l)]

/-- This proves only the second inequality of q28. The first inequality is
the named actual-density obligation above and is never assumed implicitly. -/
theorem preferred_shell_power_comparison (d : PreferredBranchData) {N j : ℕ}
    (hN : 2 ≤ N) (l : ℤ) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) :
    r^(2*(N:ℝ)-2*(j:ℝ)-3) *
      (preferredShellScale d N l r ε)^(-(N:ℝ)+3/2) ≤ r^(shellExponent N j) :=
  every_diameter_shell_comparison hr (preferredShellScale_ge_diameter d N l r hε) hN j

end
end IsingBulk.Preferred22
