# Statement and model correspondence

This record covers the two principal theorem statements; it is not a
line-by-line audit of every auxiliary proposition in the manuscript.
Successful proof checking is recorded separately in
[VERIFICATION-94cc7117.md](VERIFICATION-94cc7117.md).

## Main speed declarations

The checked manuscript is `main_1d-3.tex`, SHA-256
`b1727fd4da2a57742e79dcab6944c2d3e491ab5fcb93ad06036ca656bfa34ec1`.

`M4Blk.main_claim` and `M4Blk.main_claim_direct` in
[Swarm/BlkMeasure.lean](../Swarm/BlkMeasure.lean) each have source premises
$1/2<p<1$ and $m\ge2$ and no additional mathematical assumptions.
They choose $\kappa>0$ **before** $N$, and then for every $N\ge2$ choose a
deterministic $v\in[\kappa,2p-1]$. Almost surely, every walker has that speed.
The two declarations are alternative final assemblies using shared
dependencies, not independent proofs of every intermediate result.

## Actual probability model

The trajectory starts all walkers at zero. Local times include visits at time
zero. At each simultaneous update, every walker reads the **old** state and
reads other walkers' local-time sums only. Its right probability is $p$ when
that sum is at least $m$, and is $1/2$ otherwise.

The independent uniform variables are indexed using coordinates `Fin N × ℤ × ℕ`, each with law uniform on $(0,1)$ under the actual product
measure. The unused coordinate $k=0$ in the array does not affect the dynamics.
The trajectory increment uses $U\le\alpha$ for movement to the right.
Local times update only after the simultaneous jumps. A `Fin N` index replaces
the manuscript's indices $1,\ldots,N$ without changing the statement; total
division by zero at time zero is irrelevant to the eventual limit.

## Conditional independence and auxiliary scope

For the genuine conditional law of revealed coordinates, use
`Swarming.Enl.enl_fresh_law` and `Swarming.Enl.condExp_pattern_enl`.
`Transition.conditional_jumpLaw` fixes exact real-valued histories, which can
have probability zero; that identity alone must not be described as a
conditional probability law. Those different statements are not premises
added to the two principal theorems.

For the diameter, `spreadZ` means maximum position minus minimum position.
The running maximum uses times $0,\ldots,n$. The branch-wise logarithmic
exponents are $2$ for $N=2$, $1$ for $N\ge3,m<N$, and $3$ for $N\ge3,m\ge N$.
The definition used in the theorem is the actual trajectory of the interacting
walkers.

No manuscript erratum is asserted here, and no assumption that every
auxiliary formulation has an unconditional proof is made.
