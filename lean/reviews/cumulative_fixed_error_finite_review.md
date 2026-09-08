# Independent review: literal fixed-error cumulative bound

Read-only review by `/root/finite_formal` of the entire final `CumulativeFixedError.lean`, SHA-256 `266e9eb0435e9e665335b633e07301ffc23dcc5d06ac911f0c9d29742a7ba961`, against combined §1.3, Corollary 1.1/(1.6), and the actual normalization/bin helpers.

**No defect found. This new module closes the precise public statement omission identified at frozen checkpoint22.** It does not substitute an every-error or uniform-in-cap analytic premise for the source's single fixed input.

The source requirement is a comparable-density estimate at one error η, with one given cap coefficient A; output should retain exactly that error and one factor `log(2N)`, for possibly empty and unequal rows of cumulative density s. `from_fixed_input` chooses `cr>0` using only dimension, fixed geometry and p≥1, before m,d,η,c,A, scale cutoff and configurations. Its input is explicitly restricted by `H.A=A` and `H.δ≤δmax`. The new subfamily helper additionally preserves `H.δ=F.δ`; thus even δmax=1/2 needs no large-scale completion.

Actual original-index restriction, exact-cardinality row trimming and the existing proved family normalization supply the input configuration. Its cap coefficient is exactly the original one, and its union lies in the original union. Positive integer bins use a separate zero class and a count budget from geometric `C/δ`, independent of log(1/s). The weighted Jensen argument is used only for p≥1 and loses one bin count, not its pth power. It handles p=1, s=0, arbitrarily small s, empty individual rows and M=0.

`linear_bin_budget` exports the formerly local logarithmic calculation: an actual J has `C/δ≤2^J` and `J+2≤B log(2/δ)`. B depends only on C. It uses `log 2>0` and works at δ=1; it never assumes `log(2/δ)≥1`. The final constant is `cr=1/((4C)^p B)`, and division by the positive logarithm produces exactly the claimed one-log loss. No ε is spent or halved.

`source_notation` uses `(1/δ)^(b-m-η)=δ^(m-b+η)` for actual positive δ and changes only notation, not an exponent or the admissible input family. Its output denominator is literally `log(2*(1/δ))`. This is the source formula under N=1/δ, with the source's fixed geometric constants made explicit. The extra cutoff parameter is stronger than required and harmless when set to1 or1/2.

The source is clean-built and frozen outside the 406-module checkpoint. Its exact-source audit was running when review was completed; the parent/scalar own that audit and subsequent integrated freeze. This review does not edit or retroactively strengthen frozen `CumulativeEstimate.lean` or checkpoint22's published scope.
