# Bilinear Maps with Fewer AND Gates than Rank — Complete Proof

Author: Yuki Obuchi

All arithmetic is over $\mathbb F_2$. Variables are Boolean, so $x_k^2=x_k$, and we compute Boolean functions, i.e. elements of $\mathbb F_2[x,y]/(x_k^2-x_k,\ y_s^2-y_s)$, not formal polynomials.

## 1. Definitions and results

A bilinear map $\varphi:\mathbb F_2^{n_x}\times\mathbb F_2^{n_y}\to\mathbb F_2^{d}$ is given by its coefficient tensor $\varphi[k,s,a]$:
$$
\varphi_a(x,y)=\sum_{k,s}\varphi[k,s,a]\,x_k y_s\qquad(a=1,\dots,d).
$$
Its (tensor, or bilinear) rank $R(\varphi)$ is the least $r$ such that $\varphi=\sum_{\rho=1}^{r}u_\rho\otimes v_\rho\otimes w_\rho$.

Circuits consist of fan-in-two AND gates, and XOR gates and constants, which are free.

- $\mathrm{MC}(\varphi)$ (multiplicative complexity) is the least number of AND gates in any circuit computing $\varphi_1,\dots,\varphi_d$.
- $\mathrm{qMC}(\varphi)$ is the least number of AND gates in a quadratic circuit: every AND gate multiplies two affine functions of the inputs (AND-depth one), and each output is an affine combination of AND gates and inputs. These are the level-one circuits $L_1$ of Mirwald–Schnorr and the quadratic circuits of Boyar–Find.

**Theorem 1 (universal two-layer frame).** Let $n=4^N$. Every bilinear map $\varphi:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^n$ is computed by a circuit of AND-depth two with exactly
$$
12^N+12^N=2\,n^{\log_4 12}\qquad(\log_4 12=1.79248\ldots)
$$
AND gates. All linear forms entering the AND gates and all output assignments are independent of $\varphi$; only a 0/1 wiring matrix depends on $\varphi$. For arbitrary $n$, $\mathrm{MC}(\varphi)\le 24\,n^{\log_4 12}$.

**Theorem 2 (polynomial gap).** Let $n=4^N$. For all but a $2^{-n}$ fraction of the bilinear maps $\varphi:\mathbb F_2^n\times\mathbb F_2^n\to\mathbb F_2^n$:

1. if $N\ge 7$, then $\mathrm{MC}(\varphi)\le 2\cdot 12^N<n^2/3\le R(\varphi)$;
2. if $N\ge 9$, then $\mathrm{MC}(\varphi)\le 2\cdot 12^N<n^2/6\le \mathrm{qMC}(\varphi)$.

The ratio $\mathrm{qMC}(\varphi)/\mathrm{MC}(\varphi)$ is at least $n^{2-\log_4 12}/12=n^{0.2075\ldots}/12$, so it is unbounded.

The proof of Theorem 1 is constructive. The proof of Theorem 2 combines Theorem 1 with a counting bound, so it shows existence only: it gives no explicit $\varphi$.

## 2. Two-layer frames

**Definition.** A frame of shape $(n_x,n_y,d)$ with $m$ gates and $t$ products consists of

- linear forms $\xi_j$ in $x$ and $\eta_j$ in $y$ ($j=1,\dots,t$),
- linear forms $\lambda_i$ in $x$ and output sets $c_i\subseteq\{1,\dots,d\}$ ($i=1,\dots,m$).

A wiring is a 0/1 matrix $Q\in\mathbb F_2^{m\times t}$. The frame with wiring $Q$ is the circuit
$$
p_j=\xi_j(x)\,\eta_j(y),\qquad h_i=\lambda_i(x)\cdot\sum_j Q_{ij}\,p_j,\qquad \mathrm{out}_a=\sum_{i:\,a\in c_i}h_i .
$$
It has exactly $t+m$ AND gates and AND-depth two. The frame is universal if every bilinear map of its shape is computed by some wiring.

Write $c_i[a]=1$ if $a\in c_i$, and define the 4-index tensor
$$
\Omega[k,l,s,a]=\sum_{i,j}Q_{ij}\,\lambda_i[k]\,c_i[a]\,\xi_j[l]\,\eta_j[s].
$$

**Lemma 1 (criterion).** The circuit computes the bilinear map $\varphi$ if and only if, for all $s,a$,

- $\Omega[k,l,s,a]=\Omega[l,k,s,a]$ for $k\ne l$, and
- $\Omega[k,k,s,a]=\varphi[k,s,a]$.

*Proof.* As a formal polynomial, $\mathrm{out}_a=\sum_{k,l,s}\Omega[k,l,s,a]\,x_kx_ly_s$. As a Boolean function, $x_kx_ky_s=x_ky_s$, so
$$
\mathrm{out}_a=\sum_{k,s}\Omega[k,k,s,a]\,x_ky_s+\sum_{k<l,\,s}\bigl(\Omega[k,l,s,a]+\Omega[l,k,s,a]\bigr)x_kx_ly_s .
$$
Distinct multilinear monomials are linearly independent as Boolean functions (uniqueness of the algebraic normal form), so $\mathrm{out}_a=\varphi_a$ if and only if the two conditions hold. ∎

Since $\Omega$ is linear in $Q$, a frame is universal as soon as every basis tensor $e_k\otimes e_s\otimes e_a$ has a wiring. A general $\varphi$ then uses the sum of the basis wirings.

## 3. Two small frames

Index the coordinates by $1,2$.

**Lemma 2 (type A).** The frame of shape $(2,2,2)$ with $m=3$ gates and $t=4$ products is universal:

- gates $(\lambda;c)$: $(x_1;\{1\})$, $(x_2;\{2\})$, $(x_1+x_2;\{1,2\})$;
- products: all $x_ky_s$, $k,s\in\{1,2\}$.

*Proof.* Write the target as $\varphi_1=x_1\alpha_1(y)+x_2\beta_1(y)$ and $\varphi_2=x_1\alpha_2(y)+x_2\beta_2(y)$ with linear $\alpha_a,\beta_a$. Any bilinear $q_i=x_1a_i(y)+x_2b_i(y)$ is a sum of products, so it is available as a wire sum. Using $x_1^2=x_1$:
$$
\begin{aligned}
x_1q_1+(x_1+x_2)q_3&=x_1(a_1+a_3)+x_2b_3+x_1x_2(b_1+a_3+b_3),\\
x_2q_2+(x_1+x_2)q_3&=x_1a_3+x_2(b_2+b_3)+x_1x_2(a_2+a_3+b_3).
\end{aligned}
$$
Choose
$$
a_3=\alpha_2,\quad b_3=\beta_1,\quad a_1=\alpha_1+\alpha_2,\quad b_1=\alpha_2+\beta_1,\quad a_2=\alpha_2+\beta_1,\quad b_2=\beta_1+\beta_2 .
$$
The cubic terms cancel and the outputs are $\varphi_1,\varphi_2$. ∎

**Lemma 3 (type B).** The frame of shape $(2,2,2)$ with $m=4$ gates and $t=3$ products is universal:

- products: $p_1=x_1y_1$, $p_2=x_2y_2$, $p_3=(x_1+x_2)(y_1+y_2)$;
- gates: $(x_u;\{a\})$ for $u,a\in\{1,2\}$.

*Proof.* Note that $p_1+p_2+p_3=x_1y_2+x_2y_1$. Each monomial is a sum of gates with multiplier $x_1$ or $x_2$:
$$
x_1y_1=x_1\cdot p_1,\qquad x_2y_2=x_2\cdot p_2,
$$
$$
x_1y_2=x_1\cdot(p_1+p_2+p_3)+x_2\cdot p_1,\qquad x_2y_1=x_2\cdot(p_1+p_2+p_3)+x_1\cdot p_2 .
$$
For example, $x_1(x_1y_2+x_2y_1)+x_2x_1y_1=x_1y_2$. For output $a$, add up these expressions over the monomials of $\varphi_a$. The terms with multiplier $x_u$ combine into the single gate $(x_u;\{a\})$. ∎

Type A is "full products, few gates" and type B is the dual, "few products (Karatsuba), full gates". The saving in both comes from $x\cdot(xz)=xz$, which lets a second-layer gate cancel the cubic cross terms created by another gate.

## 4. Tensor products and the proof of Theorem 1

Let $F_1,F_2$ be frames of shapes $(n_1,s_1,d_1)$ and $(n_2,s_2,d_2)$. Their product $F_1\otimes F_2$ has shape $(n_1n_2,s_1s_2,d_1d_2)$. Its coordinates are pairs, so $x\in\mathbb F_2^{n_1}\otimes\mathbb F_2^{n_2}$, and it has

- gates $(\lambda_{i_1}\otimes\lambda_{i_2};\ c_{i_1}\times c_{i_2})$,
- products $(\xi_{j_1}\otimes\xi_{j_2})(x)\cdot(\eta_{j_1}\otimes\eta_{j_2})(y)$.

So it has $m_1m_2$ gates and $t_1t_2$ products. The forms $\lambda_{i_1}\otimes\lambda_{i_2}$, $\xi_{j_1}\otimes\xi_{j_2}$, $\eta_{j_1}\otimes\eta_{j_2}$ are again linear forms.

**Lemma 4.** If $F_1$ and $F_2$ are universal, so is $F_1\otimes F_2$.

*Proof.* Let $Q_1$ compute $\varphi_1$ in $F_1$ and $Q_2$ compute $\varphi_2$ in $F_2$. With the wiring $Q_1\otimes Q_2$, the definition of $\Omega$ gives
$$
\Omega[(k_1,k_2),(l_1,l_2),(s_1,s_2),(a_1,a_2)]=\Omega_1[k_1,l_1,s_1,a_1]\;\Omega_2[k_2,l_2,s_2,a_2].
$$
By Lemma 1, $\Omega_1$ and $\Omega_2$ are symmetric in their first two indices, so $\Omega$ is too. Its diagonal is $\varphi_1\otimes\varphi_2$. By Lemma 1 again, $Q_1\otimes Q_2$ computes $\varphi_1\otimes\varphi_2$.

Every basis tensor of the product shape is such a tensor product of basis tensors. By linearity (end of §2), every bilinear map of the product shape has a wiring. ∎

*Proof of Theorem 1.* By Lemmas 2–4, type A $\otimes$ type B is a universal frame of shape $(4,4,4)$. It has $3\cdot4=12$ gates and $4\cdot3=12$ products. Its $N$-th tensor power is a universal frame of shape $(4^N,4^N,4^N)$ with $12^N$ gates and $12^N$ products, which gives $2\cdot12^N$ AND gates.

For arbitrary $n$, choose $N$ with $4^{N-1}<n\le4^N$. Embed $\varphi$ in shape $(4^N,4^N,4^N)$ by padding with zero coordinates, and set the unused inputs to the constant $0$. Then $2\cdot12^N=24\cdot12^{N-1}<24\,n^{\log_4 12}$. ∎

The base frame is fully explicit. `verify.py` builds it and checks the following:

- the base frame computes each of the 64 basis tensors on all 256 inputs;
- its wiring is the unique solution of the 160 linear equations of Lemma 1 (rank 144);
- the $N=2$ frame computes random dense targets as exact reduced polynomials.

## 5. Lower bounds

**Lemma 5.** For every bilinear map $\varphi$, $\mathrm{qMC}(\varphi)\ge R(\varphi)/2$.

*Proof.* Take a quadratic circuit with AND gates $g_r=A_rB_r$ ($r=1,\dots,k$), where $A_r=\alpha_r(x)+\alpha'_r(y)+\epsilon_r$ and $B_r=\beta_r(x)+\beta'_r(y)+\epsilon'_r$ are affine.

A monomial $x_ky_s$ can arise in the product $A_rB_r$ only as $x_k\cdot y_s$ or $y_s\cdot x_k$. Reducing $x_k^2\to x_k$ never creates or destroys such a monomial. So the $x$–$y$ part of the reduced polynomial of $g_r$ is the bilinear form $\alpha_r\otimes\beta'_r+\beta_r\otimes\alpha'_r$, which has rank at most two.

Each output is an affine combination of the $g_r$ and the inputs. By uniqueness of the reduced polynomial, its coefficient tensor in the monomials $x_ky_s$ equals $\varphi_a$. Hence $\varphi=\sum_r(\alpha_r\otimes\beta'_r+\beta_r\otimes\alpha'_r)\otimes w_r$, where $w_r$ records the outputs that use $g_r$. This is a sum of $2k$ rank-one tensors, so $R(\varphi)\le 2k$. ∎

**Lemma 6 (counting).** Let $n=4^N$. At most a $2^{-n}$ fraction of the tensors in $\mathbb F_2^{n}\otimes\mathbb F_2^{n}\otimes\mathbb F_2^{n}$ have rank $<n^2/3$.

*Proof.* There are at most $(2^n)^{3r}=2^{3nr}$ sums of $r$ rank-one tensors $u\otimes v\otimes w$. Since $n^2\equiv1\pmod 3$, rank $<n^2/3$ means rank $\le r=(n^2-1)/3$. For this $r$, $3nr=n^3-n$, so these tensors form at most a $2^{3nr}/2^{n^3}=2^{-n}$ fraction. ∎

*Proof of Theorem 2.* By Theorem 1, $\mathrm{MC}(\varphi)\le2\cdot12^N$ for every $\varphi$. By Lemma 6, outside a $2^{-n}$ fraction we have $R(\varphi)\ge n^2/3=16^N/3$, and then $\mathrm{qMC}(\varphi)\ge16^N/6$ by Lemma 5.

The inequality $2\cdot12^N<16^N/3$ is equivalent to $(4/3)^N>6$, which holds exactly for $N\ge7$. The inequality $2\cdot12^N<16^N/6$ is equivalent to $(4/3)^N>12$, which holds exactly for $N\ge9$ ($n=262{,}144$). Finally, $\mathrm{qMC}/\mathrm{MC}\ge(16^N/6)/(2\cdot12^N)=(4/3)^N/12=n^{\log_4(4/3)}/12$. ∎

## 6. Remarks and scope

1. **Counting lower bound for MC.** A circuit with $s$ AND gates is determined by the affine inputs of each gate and by the outputs, each an affine combination of the earlier gates and the $2n$ inputs. So there are at most $2^{(2s+n)(s+2n+1)}$ such circuits. Computing all $2^{n^3}$ bilinear maps therefore requires $s=\Omega(n^{3/2})$ for most of them. The generic value of $\mathrm{MC}$ thus lies between $\Omega(n^{3/2})$ and $O(n^{1.7925})$. The best exponent of a universal frame is open.

2. **Why the asymmetry matters.** Identify the $x$- and $y$-coordinates, and suppose every wire sum $q_i=\sum_jQ_{ij}p_j$ is a symmetric bilinear form. Put $S(u,v,w)=\sum_i c_i\,\lambda_i(u)\,q_i(v,w)$ for an output combination $c$. If the output is bilinear, Lemma 1 says that $S$ is symmetric in its first two arguments. Since each $q_i$ is symmetric, $S$ is also symmetric in its last two arguments, so $S(x,x,y)=S(y,x,x)=\sum_ic_i\,\lambda_i(y)\,q_i(x,x)$. Hence every computed form lies in the span of the $t$ products and of the $m$ rank-one forms $q_i(x,x)\lambda_i(y)$. Such circuits never beat the rank. In types A and B the wire sums are not symmetric.

3. **What is not claimed.**
   - Nothing is said about explicit maps: Theorem 2 is an existence statement.
   - Nothing is said about matrix multiplication. With $n=k^2$, Theorem 1 gives $O(k^{3.585})$, which is worse than the trivial $k^3$.
   - Nothing is said about asymptotic rank.
   - Nothing is said about total circuit size. The wiring matrices are dense, so the frames use about $n^{3.585}$ XOR gates. Counting shows that most bilinear maps need total size $\Omega(n^3/\log n)$ anyway.
   - For $N\le8$ the counting argument does not guarantee a gap. This does not show that no gap exists there.

4. **Relation to quadratic-circuit optimality.** Mirwald and Schnorr asked whether $L=L_1$ for sets of quadratic forms; equality is known for one or two forms. An explicit set with $\mathrm{MC}=6<7=\mathrm{qMC}$ is given in the companion note *Six AND Gates Beat Seven* (doi:10.5281/zenodo.24525440). Theorem 2 shows that the ratio $L_1/L$ is not even bounded, already for bilinear maps.
