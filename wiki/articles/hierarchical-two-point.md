---
{
  "id": "hierarchical-two-point",
  "title": "Critical two-point function on the hierarchical lattice",
  "subtitle": "A model-specific power law with a reusable dependency chain.",
  "kind": "theorem",
  "category": "Hierarchical percolation",
  "summary": "For a radial hierarchical kernel comparable to a power law, critical connection probabilities have a matching power-law upper and lower bound throughout the regime 0 < α < d.",
  "context": [
    "Integers $d\\ge1$ and $L\\ge2$ define the hierarchical lattice.",
    "The intensity kernel $J$ is nonnegative and symmetric, $J(x)=J(-x)$. It is radial, depending only on the hierarchical distance, only where a statement says so.",
    "Edges are independent, with probabilities $1-\\exp(-\\beta J(x-y))$ at intensity $\\beta\\ge0$."
  ],
  "related": [
    "sharpness",
    "universal-tightness",
    "triangle-condition",
    "cutoff-families"
  ],
  "sourceIds": [
    "hutchcroft-hierarchical-2021",
    "hutchcroft-book"
  ],
  "aliases": [
    "hierarchical lattice",
    "hierarchical two-point function",
    "ultrametric",
    "hierarchical long-range percolation",
    "critical two point"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "criticality",
    "susceptibility"
  ]
}
---

## The hierarchical geometry {#section-model}

<a id="tag-XMYD" data-assertion="definition" data-title="Hierarchical lattice"></a><p>The vertex group is</p>
      $$\mathbb H_L^d=\bigoplus_{i\ge1}(\mathbb Z/L\mathbb Z)^d.$$
      <a id="tag-T6SL" data-assertion="definition" data-title="Hierarchical distance and ball volume"></a><p>Vertices are sequences with only finitely many nonzero coordinates. For $x\ne y$, their distance is $L^{\max\{i:x_i\ne y_i\}}$, and the distance from a vertex to itself is zero. A radius-$L^n$ ball contains $L^{dn}$ vertices.</p>
      <a id="tag-JCRB" data-assertion="definition" data-title="Smallest common hierarchical ball and regularized distance"></a><p>For vertices $x,y$, let $\Lambda(x,y)$ be the smallest hierarchical ball containing them, and put $\langle x-y\rangle=\max\{1,\|x-y\|\}$. A radial kernel depends only on this distance.</p><p>The <a href="#/product-model">independent intensity law</a> assigns an edge probability determined by its kernel value and the intensity parameter.</p>

## The critical estimate {#section-statement}

<a id="tag-J98J" data-assertion="theorem" data-title="Critical averaged two-point estimate"></a><div class="theorem-statement"><p>Let $0&lt;\alpha&lt;d$, let $J$ be symmetric and integrable, and suppose that there are constants $c,C&gt;0$ such that</p>
      $$c\|x\|^{-d-\alpha}\le J(x)\le C\|x\|^{-d-\alpha}
      \qquad(x\ne0).$$
      <p>For $n\ge0$ let $\Lambda_n=\{x:\|x\|\le L^n\}$ be the hierarchical ball of radius $L^n$ about the origin, so that $|\Lambda_n|=L^{dn}$. Then the <a href="#/criticality">critical intensity</a> satisfies $\beta_c&lt;\infty$, and there are constants $a,A&gt;0$, depending only on $d,L,\alpha,c,C$, such that, for every $n\ge1$,</p>
      $$aL^{-(d-\alpha)n}
      \le \frac1{|\Lambda_n|}\sum_{x\in\Lambda_n\setminus\Lambda_{n-1}}\mathbb P_{\beta_c}\bigl(0\leftrightarrow x\text{ inside }\Lambda_n\bigr)
      \le \frac1{|\Lambda_n|}\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)
      \le AL^{-(d-\alpha)n}.$$</div>
      <p>The kernel need not be radial. Integrability already follows from the upper bound, because $\alpha&gt;0$. The sum over the shell $\Lambda_n\setminus\Lambda_{n-1}$ is divided by the volume of the whole ball, as in the source; the shell has $(1-L^{-d})L^{dn}$ vertices, so the two normalisations differ by a bounded factor.</p>
      <p><em>Proof.</em> There are $(1-L^{-d})L^{dj}$ vertices at distance $L^j$ from the origin, so the upper bound on $J$ gives the finite row sum</p>
      $$B=\sum_{x\ne0}J(x)\le CK,\qquad K=\frac{(1-L^{-d})L^{-\alpha}}{1-L^{-\alpha}}.$$
      <p>The kernel is translation invariant and symmetric and satisfies the lower bound of <a href="/tag/7AER/">the amplification theorem</a>, whose constant $A_0$ depends only on $c,d,L,\alpha$. Hence <a href="/tag/FF30/">the critical-intensity theorem</a> gives $1/(CK)\le1/B\le\beta_c\le A_0/4&lt;\infty$, finite susceptibility below $\beta_c$, the critical quantile estimate, and the boundary-flux inequality for every finite set containing the origin, in particular for every $\Lambda_n$. The <a href="/tag/12NL/">rooted-tail theorem</a> supplies rooted damping in each finite block. Thus <a href="/tag/655W/">the expected-size theorem</a> and <a href="/tag/7YNX/">the conditional two-point theorem</a> apply at $b=\beta_c$ with $C_0=C$: for $n\ge1$ and $x\in\Lambda_n\setminus\Lambda_{n-1}$,</p>
      $$c_1L^{-(d-\alpha)n}\le\mathbb P_{\beta_c}\bigl(0\leftrightarrow x\text{ inside }\Lambda_n\bigr)\le\mathbb P_{\beta_c}(0\leftrightarrow x)\le C_1L^{-(d-\alpha)n}.$$
      <p>These constants depend only on $d,L,\alpha,c,C$. In the proofs of those two theorems the constants are explicit functions of $b,c,C_0,A_0,d,L,\alpha$: the truncation level $T=cA_0t^2L^{-(d+\alpha)}$ does not involve $b$, the lower constant $c_1=ce^{-T}L^{-2\alpha}/(4bD^2)$ decreases in $b$, and $C_1=bC_0(C')^2/(1-L^{-(d-\alpha)})$ with $C'=4e^TL^{d+2\alpha}/(bc)$ is a fixed multiple of $1/b$. The kernel enters beyond $c$ and $C$ only through $b=\beta_c$, which lies in $[1/(CK),A_0/4]$, so one may take $c_1$ at $b=A_0/4$ and $C_1$ at $b=1/(CK)$.</p>
      <p>Summing the lower bound over the shell gives the first inequality with $a=(1-L^{-d})c_1$. The middle inequality holds because a connection inside $\Lambda_n$ is a connection, and the shell is part of the ball. For the last, the origin contributes $1$ and the shell at distance $L^k$ contributes at most $L^{dk}\cdot C_1L^{-(d-\alpha)k}=C_1L^{\alpha k}$, so</p>
      $$\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)\le1+C_1\sum_{k=1}^nL^{\alpha k}\le\Bigl(1+\frac{C_1}{1-L^{-\alpha}}\Bigr)L^{\alpha n}.$$
      <p>Dividing by $|\Lambda_n|=L^{dn}$ gives the upper bound with $A=1+C_1/(1-L^{-\alpha})$.</p>
      <a id="tag-W498" data-assertion="theorem" data-title="Critical pointwise two-point estimate for radial kernels"></a><div class="theorem-statement"><p>Let $0&lt;\alpha&lt;d$, let $J$ be radial, and suppose that there are constants $c,C&gt;0$ such that</p>
      $$c\|x\|^{-d-\alpha}\le J(x)\le C\|x\|^{-d-\alpha}
      \qquad(x\ne0).$$
      <p>Then the <a href="#/criticality">critical intensity</a> satisfies $0&lt;\beta_c&lt;\infty$, and there are constants $a,A&gt;0$, depending only on $d,L,\alpha,c,C$, such that, for every $x,y\in\mathbb H_L^d$,</p>
      $$a\langle x-y\rangle^{-d+\alpha}
      \le \mathbb P_{\beta_c}\bigl(x\leftrightarrow y\text{ inside }\Lambda(x,y)\bigr)
      \le \mathbb P_{\beta_c}(x\leftrightarrow y)
      \le A\langle x-y\rangle^{-d+\alpha}.$$</div>
      <p>The lower bound already holds with <a href="#/connectivity">paths restricted to one ball</a>. The upper bound permits paths in the entire lattice.</p>
      <p>In the source this corollary is deduced from <a href="/tag/J98J/">the averaged estimate</a> by averaging over shells, and that step is where radiality is used. For a radial kernel the isometries of the hierarchical lattice preserve the law, so both connection probabilities from the origin are constant on each shell $\Lambda_n\setminus\Lambda_{n-1}$; the averaged bounds then become pointwise bounds, with the constants changed by at most the factor $(1-L^{-d})^{-1}$, and translation moves a pair $x,y$ with $\|x-y\|=L^n$ to the pair $0,y-x$, for which $\Lambda(x,y)$ becomes $\Lambda_n$. The pointwise bounds do not need radiality. For a symmetric translation-invariant kernel with the same two-sided bounds, <a href="/tag/7YNX/">the conditional two-point theorem</a>, with its inputs supplied as in the proof of the averaged estimate, gives them directly.</p>

## A ball susceptibility calculation {#section-consequence}

<a id="tag-V4QQ" data-assertion="corollary" data-title="Full-cluster susceptibility in a hierarchical ball"></a><p>The pointwise estimate immediately determines the <a href="#/susceptibility">finite-region susceptibility</a>, namely the expected mass of the full cluster inside a ball. The shell at distance $L^k$ contains $L^{dk}-L^{d(k-1)}$ vertices. Multiplying by a connection probability of order $L^{-k(d-\alpha)}$ gives a shell contribution of order $L^{\alpha k}$. Summing the geometric series yields</p>
      $$\mathbb E_{\beta_c}|K_0\cap\Lambda_n|
        =\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)
        \asymp L^{\alpha n}.$$
      <a id="tag-YWTU" data-assertion="corollary" data-title="Restricted-cluster susceptibility in a hierarchical ball"></a><p>The restricted lower estimate also gives the same order for the cluster formed using only edges inside $\Lambda_n$. These are distinct observables with matching orders in this theorem.</p>

## Symmetry and further estimates {#section-position}

<p>Radial symmetry makes vertices on the same shell equivalent, relating averaged connection estimates to pointwise bounds. Critical estimates combine this multiscale geometry with general tools such as <a href="#/sharpness">sharpness</a> and <a href="#/universal-tightness">cluster tightness</a>.</p>
      <p>The spatial estimate supplies an input to <a href="#/triangle-condition">triangle-diagram calculations</a>. Cluster-volume tails, finite-size scaling, and statements at a marginal exponent need their own hypotheses and proofs; they should not be silently attached to this result.</p>
