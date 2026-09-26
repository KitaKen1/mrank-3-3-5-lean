# A Lean proof that the maximal rank of complex 3 × 3 × 5 tensors is 6

This repository formalizes a solution to the open statement
`Arxiv.«0805.3777».isMaxRank_three_three_five` registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Arxiv/0805.3777/TensorRank.lean).
The rank of a tensor $`T\in\mathbb C^3\otimes\mathbb C^3\otimes\mathbb C^5`$ is the least number of
decomposable tensors $`a\otimes b\otimes c`$ whose sum is $`T`$ (Mathlib's `Holor.cprank`), and the
maximal rank $`\operatorname{mrank}(3,3,5)`$ is the largest rank attained by such a tensor. The
theorem is

```text
mrank(3, 3, 5) = 6:   every complex 3 × 3 × 5 tensor has rank at most 6,
                      and some complex 3 × 3 × 5 tensor has rank exactly 6.
```

Previously only $`\operatorname{mrank}(3,3,5)\in\{6,7\}`$ was known. It was the one undetermined
entry of the table of $`\operatorname{mrank}(3,3,p)`$ for $`p\le 9`$ (Bruzda–Friedland–Życzkowski,
(4.20), based on Atkinson–Stephens).

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fmrank-3-3-5-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FTensorRank335Lean4Web.lean)
(for "Latest Mathlib with Lean v4.35.0-rc3"; the file is long, so elaboration takes a few minutes)

## Formal Conjectures target

The file in `lean/` imports the Formal Conjectures statement file and proves the statement with the
answer `6`. The definition `IsMaxRank` is the one imported from Formal Conjectures, and the rank
is Mathlib's `Holor.cprank`.

```lean
theorem TensorRank335.isMaxRank_three_three_five_solved :
    Arxiv.«0805.3777».IsMaxRank [3, 3, 5] answer(6)

theorem TensorRank335.isMaxRank_three_three_five_bounds_solved {R : ℕ}
    (hR : Arxiv.«0805.3777».IsMaxRank [3, 3, 5] R) : 6 ≤ R ∧ R ≤ 7
```

Here `IsMaxRank ds r := IsGreatest (Set.range fun T : Holor ℂ ds => T.cprank) r`. The theorem
`Arxiv.«0805.3777».isMaxRank_three_three_five` can therefore be changed from `research open` to
`research solved` by replacing its answer hole with `6` and using this proof. The second theorem is
the file's `research solved` statement `isMaxRank_three_three_five_bounds`, which Formal
Conjectures states without a proof.

## Mathematical explanation (AI generated)

**Notation.** Let $`M=M_3(\mathbb C)`$ with the bilinear pairing
$`\langle X,B\rangle=\sum_{i,j}X_{ij}B_{ij}`$, and for a subspace $`S\subseteq M`$ let
$`\operatorname{ann}S=\{B:\langle X,B\rangle=0\ \text{for all}\ X\in S\}`$. For $`a,b\in\mathbb C^3`$
we have $`\langle ab^{\mathsf T},B\rangle=a^{\mathsf T}Bb`$. Write $`[b]_\times`$ for the matrix of
$`v\mapsto b\times v`$.

### 0. Tensors and spaces of matrices

Let $`T_1,\dots,T_5\in M`$ be the slices of $`T`$ along the last index. Then
$`\operatorname{rank}T\le r`$ if and only if $`\operatorname{span}(T_1,\dots,T_5)`$ lies in the span
of $`r`$ rank-one matrices. So it suffices to show:

```math
\text{every subspace } S\subseteq M \text{ with } \dim S\le 5 \text{ lies in the span of six rank-one matrices,}
```

and to exhibit one five-dimensional $`S`$ for which five rank-one matrices do not suffice. We may
assume $`\dim S=5`$, and then $`V=\operatorname{ann}S`$ is four-dimensional, with basis
$`B_0,\dots,B_3`$.

### 1. The lower bound

Take the slices $`E_{12},E_{13},E_{23},E_{11}-E_{22},E_{22}-E_{33}`$. They span the space $`S_0`$
of trace-zero upper-triangular matrices, which has dimension $`5`$. If $`S_0`$ lay in the span of
five rank-one matrices, these would span exactly $`S_0`$, so they would all lie in $`S_0`$. A
rank-one matrix $`ab^{\mathsf T}\in S_0`$ has zero diagonal, since
$`(a_ib_i)^2=a_ib_i\operatorname{tr}(ab^{\mathsf T})-\sum_{j\ne i}(a_ib_j)(a_jb_i)=0`$. But then no
combination of them has $`(1,1)`$ entry $`1`$. Hence the rank is $`6`$, attained by the six
upper-triangular matrix units.

### 2. Lemma R: a squarefree cubic forces enough rank-one matrices

Let $`B_0,B_1,B_2\in M`$, put $`K(b)=[B_0b\mid B_1b\mid B_2b]`$ (columns), and consider the ternary
cubic $`f(b)=\det K(b)`$.

**Lemma R.** Suppose $`f`$ is squarefree. If $`A\in M`$ satisfies $`a^{\mathsf T}Ab=0`$ whenever
$`a^{\mathsf T}B_kb=0`$ for $`k=0,1,2`$, then $`A\in\operatorname{span}(B_0,B_1,B_2)`$.

*Proof.*
1. If $`f(b)=0`$, each row $`r`$ of $`\operatorname{adj}K(b)`$ satisfies $`rK(b)=0`$, so
   $`r\,B_kb=0`$ for all $`k`$. The hypothesis gives $`r\,Ab=0`$. Hence every entry of
   $`P(b)=\operatorname{adj}K(b)\,A\,b`$ vanishes on the zero set of $`f`$.
2. By the Nullstellensatz and squarefreeness, $`f`$ divides each entry of $`P`$. Both are cubic, so
   $`P=f\cdot c`$ for a constant vector $`c`$.
3. Multiplying by $`K`$ gives $`f\cdot Ab=f\cdot K(b)c`$, i.e. $`Ab=\sum_kc_kB_kb`$ for all $`b`$.
   So $`A=\sum_kc_kB_k`$. $`\square`$

By duality, the six-dimensional space $`\operatorname{ann}\operatorname{span}(B_0,B_1,B_2)`$ is then
spanned by its rank-one elements. Hence every $`S`$ annihilated by $`B_0,B_1,B_2`$ lies in the span
of six rank-one matrices. In operator-theoretic language, this says that
$`\operatorname{span}(B_k)`$ is reflexive.

### 3. The linear system of hyperplanes of $`V`$

Let $`m_0,\dots,m_3`$ be the $`3\times3`$ minors of $`[B_0b\mid B_1b\mid B_2b\mid B_3b]`$. They are
normalized so that the hyperplane $`\operatorname{span}(B_j+c_jB_3)_{j<3}`$ has column cubic
$`m_3+\sum_{j<3}c_jm_j`$. By Laplace expansion of a determinant with a repeated row,

```math
m_0\,B_0b+m_1\,B_1b+m_2\,B_2b=m_3\,B_3b .
```

### 4. A Bertini theorem for pencils of plane cubics

**Pencil lemma.** Let $`f,g`$ be ternary cubics. If $`f+tg`$ is not squarefree for any $`t\in\mathbb C`$,
then $`p^2\mid f`$ and $`p^2\mid g`$ for some linear $`p`$.

*Proof.* The dependent case is direct, so assume $`f,g`$ are linearly independent.
1. For six values of $`t`$, pick a linear $`p_t`$ with $`p_t^2\mid f+tg`$.
2. If two of the $`p_t`$ are associated, that $`p_t^2`$ divides $`g`$ and hence $`f`$, and we are done.
3. Otherwise each $`p_t`$ divides $`f\,\partial_jg-g\,\partial_jf=(f+tg)\,\partial_jg-g\,\partial_j(f+tg)`$.
   This polynomial has degree $`\le5`$ but six distinct linear factors, so $`f\,\partial_jg=g\,\partial_jf`$
   for all $`j`$.
4. Comparing leading coefficients for a monomial order shows that this forces $`f`$ and $`g`$ to be
   proportional, a contradiction. $`\square`$

Consequently, if no hyperplane of $`V`$ has a squarefree column cubic, then all four minors are
divisible by a common $`p^2`$.

### 5. The one-sided trichotomy

Exactly one of the following holds.
- **(A)** Some hyperplane of $`V`$ has a squarefree column cubic. Then Lemma R covers $`S`$ by six.
- **(B)** All minors vanish. Then for every $`b`$ the four vectors $`B_kb`$ span at most a plane, so
  some $`a\ne0`$ has $`ab^{\mathsf T}\in S`$.
- **(C)** $`m_k=p^2\mu_k`$ with $`\mu\ne0`$. Dividing the syzygy by $`p^2`$ gives a nonzero linear
  map $`\Phi:\mathbb C^3\to V`$ with $`\Phi(b)b=0`$. Every such map has the form
  $`\Phi(b)=N[b]_\times`$ with $`N\ne0`$. Since
  $`\langle X,N[b]_\times\rangle=\langle N^{\mathsf T}X,[b]_\times\rangle`$, this means that
  $`N^{\mathsf T}X`$ is symmetric for every $`X\in S`$.

The same trichotomy applied to $`S^{\mathsf T}`$ gives the row version:
- (B) becomes: every $`a`$ is the row vector of a rank-one element.
- (C) becomes: $`XN'`$ is symmetric for all $`X\in S`$.

### 6. The degenerate cases

The cases are distinguished by $`\operatorname{rank}N`$ (similarly for $`N'`$).

- **$`\operatorname{rank}N=3`$.** $`S\subseteq N^{-\mathsf T}\,\mathrm{Sym}`$. The symmetric matrices are
  spanned by the six rank-one matrices $`e_ie_i^{\mathsf T}`$ and $`(e_i+e_j)(e_i+e_j)^{\mathsf T}`$.
- **$`\operatorname{rank}N=2`$.** Normalize $`N`$ to $`\operatorname{diag}(1,1,0)`$. Then
  $`S\subseteq\{X_{12}=X_{21},\,X_{13}=X_{23}=0\}`$, which is spanned by $`E_{11},E_{22}`$,
  $`(e_1+e_2)(e_1+e_2)^{\mathsf T}`$, $`E_{31},E_{32},E_{33}`$.
- **$`\operatorname{rank}N=\operatorname{rank}N'=1`$.** With $`N=uv^{\mathsf T}`$ and
  $`N'=u'v'^{\mathsf T}`$, the conditions say that $`u^{\mathsf T}X\parallel v^{\mathsf T}`$ and
  $`Xu'\parallel v'`$. After normalization these are four explicit coordinate subspaces, each spanned
  by at most six matrix units.
- **Case (B) on one side.** It gives either four linearly independent rank-one matrices in $`S`$, or
  a vector $`y`$ with $`y\,w^{\mathsf T}\in S`$ for all $`w`$. Combining the second alternative with
  (B) or (C) on the other side again produces four independent rank-one matrices. In one sub-case
  this uses that a pencil of $`2\times2`$ matrices contains a singular member.

### 7. Four rank-one matrices suffice

Suppose $`S`$ contains linearly independent rank-one matrices $`R_1,\dots,R_4`$, and write
$`S=\operatorname{span}(R_l)\oplus\langle X\rangle`$.
- If $`\det(X+\sum c_lR_l)`$ vanishes for some $`c`$, that element has rank at most $`2`$. Then
  $`4+2=6`$ rank-one matrices suffice.
- Otherwise this polynomial in $`c`$ has no zero, so it is a nonzero constant. Then
  $`\det(1+tX^{-1}\sigma)=1`$ for every $`\sigma\in\operatorname{span}(R_l)`$ and every $`t`$. So
  $`X^{-1}\operatorname{span}(R_l)`$ is a four-dimensional space of nilpotent matrices.

The second case is impossible by Gerstenhaber's bound: a linear space of nilpotent $`3\times3`$
matrices has dimension at most $`3`$. The bound is proved in the file by normalizing a rank-two
element to a Jordan block.

The argument uses no projective geometry beyond the Nullstellensatz for polynomials in three
variables.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Formal Conjectures version, pinned to commit `2424bb48...` |
| `lean4web/` | `v4.35.0-rc3` | Standalone mathlib-only proof for Lean4Web (mathlib `f35c4159...`) |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and the generated
`lake-manifest.json`. Both proof files contain the same development, in the sections `Bridge`,
`Defs`, `LowerBound`, `ReflexR`, `Pencil`, `Syzygy`, `SyzygyN`, `Nilpotent3`, `Degenerate`,
`Upper` and `Main`. The Lean4Web file also contains a copy of the definition `IsMaxRank` from
Formal Conjectures, and states the target with `6` in place of `answer(6)`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both results are kernel checked. The proof files contain no `sorry`, `admit`, custom axiom,
`native_decide`, or `unsafe` theorem. Their final `#print axioms` commands report only Lean's
standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is solved here:

```text
mrank(3, 3, 5) = 6 over ℂ  (Arxiv.«0805.3777».isMaxRank_three_three_five, answer 6),
hence also 6 ≤ mrank(3, 3, 5) ≤ 7  (Arxiv.«0805.3777».isMaxRank_three_three_five_bounds).
```

What remains open in the same Formal Conjectures file:

```text
The maximal rank of n × n × n tensors (Arxiv.«0805.3777».isMaxRank_cube).
Friedland's conjecture on generic ranks in the critical range
(Arxiv.«0805.3777».isGenericRank_of_le_critical).
```

The result is about complex tensors. The real maximal rank of $`3\times3\times5`$ tensors is not
addressed.

We are not aware of an earlier proof of $`\operatorname{mrank}(3,3,5)=6`$ in the literature, but a
literature search cannot exclude unpublished work.

## Sources

- [Formal Conjectures: `Arxiv/0805.3777/TensorRank.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Arxiv/0805.3777/TensorRank.lean)
- S. Friedland, *On the generic and typical ranks of 3-tensors*, Linear Algebra Appl. 436 (2012),
  [arXiv:0805.3777](https://arxiv.org/abs/0805.3777)
- W. Bruzda, S. Friedland and K. Życzkowski, *Rank of a tensor and quantum entanglement*, Linear
  Multilinear Algebra 72 (2024), [arXiv:1912.06854](https://arxiv.org/abs/1912.06854), (4.20)
- M. D. Atkinson and N. M. Stephens, *On the maximal multiplicative complexity of a family of
  bilinear forms*, Linear Algebra Appl. 27 (1979)
- T. Sumi, M. Miyazaki and T. Sakata, *About the maximal rank of 3-tensors over the real and the
  complex number field*, Ann. Inst. Statist. Math. 62 (2010),
  [arXiv:0806.4048](https://arxiv.org/abs/0806.4048)
- M. Gerstenhaber, *On nilalgebras and linear varieties of nilpotent matrices I*, Amer. J. Math.
  80 (1958)
- A. I. Loginov and V. S. Shulman, *Hereditary and intermediate reflexivity of W\*-algebras*, Izv.
  Akad. Nauk SSSR Ser. Mat. 39 (1975): the duality between reflexivity and spans of rank-one operators
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by
Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code
using Claude Opus 5.5.
