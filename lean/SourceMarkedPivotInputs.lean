import AbsoluteCapEstimates
import LiftedCumulativeInput
import SourceMarkedPivotFullRange

/-! The source minimum-kappa pivot from the manuscript's weaker analytic
inputs (5.4) and (5.5). The original marked configuration still uses the
normalized separation and comparable-row conventions of Hypotheses; this file
does not assert the separate arbitrary-fixed-comparability normalization.
-/
namespace KakeyaFormal.SourceMarkedPivotInputs
open Finset AdmissiblePivotSlabs
noncomputable section

/-- Source source fourth with only absolute-cap base and cumulative lifted inputs. -/
theorem source_fourth {k : ℕ} {m d d' p q : ℝ}
    (hbase : AbsoluteDiscreteEstimate (k+2) m d p)
    (hlift : LiftedCumulativeInput (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta alpha : ℝ},
      Hypotheses F E marks δ A lam xi B theta width baseRadius m alpha →
      lam ≤ 1 → xi ≤ 1 → 0 < alpha →
      PivotGeometryScale.geometryConstant (k+2) width*(1+2*width)^20 ≤
        (1/δ)*(MinPivotKappa.sourceChoice width B alpha theta)^20 →
      c*A⁻¹*(MinPivotKappa.sourceChoice width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (E.card:ℝ)^4 :=
  SourceMarkedPivotFullRange.source_fourth (hbase.to_discrete hm) hlift.to_discrete
    hm hp hd hq width baseRadius hw eps heps heps1

/-- Source source union with only absolute-cap base and cumulative lifted inputs. -/
theorem source_union {k : ℕ} {m d d' p q : ℝ}
    (hbase : AbsoluteDiscreteEstimate (k+2) m d p)
    (hlift : LiftedCumulativeInput (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius A₀ : ℝ) (hw : (1:ℝ)/12 ≤ width) (hA₀ : 1 ≤ A₀)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M)
      (marks : Fin M → Finset (Cell (k+2))) {δ lam xi B theta alpha : ℝ},
      Hypotheses F F.unionCells marks δ A₀ lam xi B theta width baseRadius m alpha →
      lam ≤ 1 → xi ≤ 1 → 0 < alpha →
      T ≤ (1/δ)*(MinPivotKappa.sourceChoice width B alpha theta)^20 →
      c*(MinPivotKappa.sourceChoice width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (F.unionCells.card:ℝ)^4 :=
  SourceMarkedPivotFullRange.source_union (hbase.to_discrete hm) hlift.to_discrete
    hm hp hd hq width baseRadius A₀ hw hA₀ eps heps heps1

/-- Source source notation with only absolute-cap base and cumulative lifted inputs. -/
theorem source_notation {k : ℕ} {m d d' p q : ℝ}
    (hbase : AbsoluteDiscreteEstimate (k+2) m d p)
    (hlift : LiftedCumulativeInput (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius A₀ : ℝ) (hw : (1:ℝ)/12 ≤ width) (hA₀ : 1 ≤ A₀)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M)
      (marks : Fin M → Finset (Cell (k+2))) {N lam xi B theta alpha : ℝ},
      2 ≤ N →
      Hypotheses F F.unionCells marks (1/N) A₀ lam xi B theta width baseRadius m alpha →
      lam ≤ 1 → xi ≤ 1 → 0 < alpha →
      T ≤ N*(MinPivotKappa.sourceChoice width B alpha theta)^20 →
      c*(MinPivotKappa.sourceChoice width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2*N))^(-(p+4))*N^(2*m+3+d'-3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)/N^m)^3 ≤ (F.unionCells.card:ℝ)^4 :=
  SourceMarkedPivotFullRange.source_notation (hbase.to_discrete hm) hlift.to_discrete
    hm hp hd hq width baseRadius A₀ hw hA₀ eps heps heps1

end
end KakeyaFormal.SourceMarkedPivotInputs
