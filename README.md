# Bilinear Maps in Fewer AND Gates than Rank

**A Polynomial Gap Between Multiplicative and Quadratic-Circuit Complexity over $\mathbb F_2$.**

[![verify](https://github.com/ObuchiYuki/bilinear-mc-gap/actions/workflows/verify.yml/badge.svg)](https://github.com/ObuchiYuki/bilinear-mc-gap/actions/workflows/verify.yml)

**Author:** Yuki Obuchi  
**First published:** 2026-11-26  
**Status:** research note (not peer-reviewed, not formally verified)

How many AND gates does a set of $n$ bilinear forms over $\mathbb F_2$ need, when XOR is free? A circuit that only multiplies affine functions (a quadratic circuit) needs about as many AND gates as the bilinear rank, which is about $n^2/3$ for almost every map. This note shows that a circuit with **two** layers of AND gates does polynomially better, for every map at once.

$$
\boxed{\ \mathrm{MC}(\varphi)\ \le\ 2\,n^{\log_4 12}=O(n^{1.7925})\quad\text{for every bilinear }\varphi:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^n\ }
$$

Therefore, for almost every bilinear map $\varphi$ (when $n=4^N\ge 4^9$),

$$
\mathrm{MC}(\varphi)\;\le\;2\cdot 12^N\;<\;\frac{n^2}{6}\;\le\;\mathrm{qMC}(\varphi),\qquad \frac{\mathrm{qMC}(\varphi)}{\mathrm{MC}(\varphi)}\ \ge\ \frac{n^{0.2075}}{12}.
$$

Here MC counts AND gates in unrestricted XOR–AND circuits, and qMC counts AND gates in quadratic circuits (the level-one circuits $L_1$ of Mirwald–Schnorr, i.e. the quadratic circuits of Boyar–Find). From $n\ge 4^7$ on, almost every map also has $\mathrm{MC}(\varphi)<R(\varphi)$, i.e. fewer AND gates than its bilinear rank.

The gap result is an existence statement, obtained by counting; no explicit map is given. The upper bound is fully constructive.

## The idea

Over $\mathbb F_2$ we compute Boolean functions, so $x\cdot x=x$. A second-layer AND gate $x_k\cdot(\text{sum of products } x_l y_s)$ creates cubic terms $x_kx_ly_s$, and these can cancel between gates. The construction uses two $2\times2\times2$ building blocks.

- **Type A** has full products and few gates: 4 products $x_ky_s$ and 3 gates with multipliers $x_1$, $x_2$, $x_1+x_2$.
- **Type B** has few products and full gates: the 3 Karatsuba products $x_1y_1$, $x_2y_2$, $(x_1+x_2)(y_1+y_2)$, and 4 gates $(x_u;\text{output }a)$. For example,
$$
x_1y_2=x_1\cdot(x_1y_2+x_2y_1)+x_2\cdot x_1y_1 .
$$

Both blocks are universal: they compute every bilinear map of their shape with a suitable XOR wiring. Their tensor product is a universal $(4,4,4)$ frame with 12 products and 12 gates. Universality is preserved by tensor powers, which gives $12^N+12^N$ AND gates for every bilinear map in dimension $4^N$.

A two-layer frame computes $\varphi$ exactly when a 4-index tensor $\Omega$ is symmetric in its two $x$-indices and has diagonal $\varphi$. The cross terms are allowed but must cancel in pairs. If the wire sums were symmetric forms, no saving would be possible (PROOF.md §6). The gain comes from asymmetric cancellation.

## Results

| Statement | Range | Type |
| :--- | :--- | :--- |
| Every bilinear $\varphi$: $\mathrm{MC}(\varphi)\le 2\cdot12^N$, AND-depth 2, fixed frame | $n=4^N$, all $N$ | constructive |
| Every bilinear $\varphi$: $\mathrm{MC}(\varphi)\le 24\,n^{1.7925}$ | all $n$ | constructive |
| $\mathrm{qMC}(\varphi)\ge R(\varphi)/2$ | all bilinear $\varphi$ | lemma |
| $R(\varphi)\ge n^2/3$ for all but a $2^{-n}$ fraction | $n=4^N$ | counting |
| $\mathrm{MC}(\varphi)<R(\varphi)$ for almost all $\varphi$ | $N\ge7$ | existence |
| $\mathrm{MC}(\varphi)<\mathrm{qMC}(\varphi)$, ratio $\ge n^{0.2075}/12$, for almost all $\varphi$ | $N\ge9$ | existence |

## Proof and verification

- [PROOF.md](PROOF.md): the complete argument.
- [verify.py](verify.py): a standalone verifier that uses only the Python standard library (Python 3.10+).

Run:

```sh
python3 verify.py          # about one second
python3 verify.py --deep   # also checks the 64 x 64 x 64 frame on random inputs
```

The verifier performs these checks:

- Types A and B compute all 256 maps of their shape, on all inputs.
- The $(4,4,4;12,12)$ base frame computes all 64 basis tensors on all 256 inputs, so by linearity it computes all $2^{64}$ maps.
- The base wiring is the unique solution of the linear system (rank 144).
- The $(16,16,16;144,144)$ frame computes random dense targets, checked as exact reduced polynomials.
- The integer thresholds $N\ge7$ and $N\ge9$ hold.

## Scope

- The upper bound counts AND gates only. The wiring matrices are dense, so the circuits have about $n^{3.585}$ XOR gates. Nothing is claimed about total circuit size.
- Nothing is claimed about explicit maps, matrix multiplication, or asymptotic rank. For matrix multiplication, $n=k^2$ gives $O(k^{3.585})$, which is worse than $k^3$.
- For $n<4^9$ (resp. $4^7$) the counting argument does not guarantee a gap, and the generic exponent is open. By counting, it lies between $3/2$ and $1.7925$.

To the best of our knowledge, the polynomial gap between MC and qMC for bilinear maps is new. This is a research note, not a peer-reviewed publication.

## References

1. Roland Mirwald and Claus-Peter Schnorr. [The multiplicative complexity of quadratic Boolean forms](https://doi.org/10.1016/0304-3975(92)90235-8). *Theoretical Computer Science* 102(2):307–328, 1992. [doi:10.1016/0304-3975(92)90235-8](https://doi.org/10.1016/0304-3975(92)90235-8). See §5, p. 325, which asks whether $L=L_1$ for all sets of quadratic forms.
2. Joan Boyar and Magnus Gausdal Find. [Multiplicative complexity of vector valued Boolean functions](https://doi.org/10.1016/j.tcs.2018.02.023). *Theoretical Computer Science* 720:36–46, 2018. [doi:10.1016/j.tcs.2018.02.023](https://doi.org/10.1016/j.tcs.2018.02.023); [arXiv:1407.6169](https://arxiv.org/abs/1407.6169).
3. Yuki Obuchi. [Six AND Gates Beat Seven: A Counterexample to Quadratic-Circuit Optimality over F2](https://doi.org/10.5281/zenodo.24525440). Research note, 2026. [doi:10.5281/zenodo.24525440](https://doi.org/10.5281/zenodo.24525440). This is the explicit single example $\mathrm{MC}=6<7=\mathrm{qMC}$.

## How to cite

Use GitHub's "Cite this repository" button, or see [CITATION.cff](CITATION.cff).

> Yuki Obuchi. *Bilinear Maps in Fewer AND Gates than Rank: A Polynomial Gap Between Multiplicative and Quadratic-Circuit Complexity over F2.* Research note, 2026.

## Acknowledgments

The construction was found, and its proofs and verifier were drafted and checked, with the help of AI assistants (Claude by Anthropic; Gemini by Google for an independent cross-check). The author reviewed the final statements.

## License

- Code ([verify.py](verify.py) and the CI configuration): [MIT License](LICENSE).
- Text, proofs and the PDF note ([README.md](README.md), [PROOF.md](PROOF.md), `paper/`): [Creative Commons Attribution 4.0 International (CC BY 4.0)](LICENSE-docs).

**Keywords:** multiplicative complexity, bilinear maps, bilinear rank, quadratic Boolean forms, XOR–AND circuits, quadratic circuit optimality, level-one multiplicative complexity, Boolean circuit complexity, tensor rank, Mirwald–Schnorr, Boyar–Find.
