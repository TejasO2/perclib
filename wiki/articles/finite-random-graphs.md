---
{
  "id": "finite-random-graphs",
  "title": "Finite random graphs and critical windows",
  "subtitle": "Use component statistics when infinite clusters are impossible.",
  "kind": "model",
  "category": "Finite-size percolation",
  "summary": "On a finite graph every cluster is finite. Component moments, largest-component scales, and critical windows replace the infinite-cluster event.",
  "context": [
    "The host graph has n ≥ 1 vertices and independent edge states.",
    "The root U is chosen uniformly from the vertices, independently of the percolation configuration.",
    "The Erdős–Rényi specialization is independent bond percolation on the complete graph K_n."
  ],
  "related": [
    "criticality",
    "exploration",
    "universal-tightness"
  ],
  "sourceIds": [
    "heydenreich-hofstad",
    "hutchcroft-book"
  ],
  "aliases": [
    "Erdős–Rényi",
    "Erdos Renyi",
    "G(n,p)",
    "finite-size scaling",
    "critical window",
    "largest component",
    "component partition"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "susceptibility",
    "subcritical-bound"
  ]
}
---

## Susceptibility from the component partition {#section-identity}

<a id="tag-CY0D" data-assertion="proposition" data-title="Conditional cluster volume from the component partition"></a><p>For a realised configuration, write its <a href="#/connectivity">connected components</a> as $C_1,\ldots,C_m$. Conditional on that configuration, a uniform root falls in $C_i$ with probability $|C_i|/n$. Therefore</p>
      $$\mathbb E\bigl[|K_U|\mid\omega\bigr]
        =\frac1n\sum_{i=1}^m|C_i|^2.$$
      <a id="tag-XCGS" data-assertion="proposition" data-title="Average susceptibility as the second component moment"></a><p>Averaging over configurations gives the finite-graph <a href="#/susceptibility">susceptibility</a>:</p>
      $$\overline\chi=\frac1n\sum_v\mathbb E|K_v|
        =\frac1n\mathbb E\sum_i|C_i|^2.$$
      <p>This identity is exact for every finite host. A fixed root has the same susceptibility as the average only when a symmetry or another argument establishes it.</p>

## A concrete subcritical calculation {#section-erdos-renyi}

<a id="tag-MIQ7" data-assertion="corollary" data-title="Subcritical Erdős–Rényi susceptibility bound"></a><p>In $G(n,p)$, the <a href="#/product-model">product law</a> opens each edge independently with probability $p$. Each vertex has $n-1$ potential neighbours, so the row sum is $(n-1)p$. The <a href="#/subcritical-bound">path-counting theorem</a> gives</p>
      $$(n-1)p&lt;1\quad\Longrightarrow\quad
      \overline\chi\le\frac1{1-(n-1)p}.$$
      <a id="tag-PXP9" data-assertion="corollary" data-title="Subcritical largest-component tail bound"></a><p>Under the same subcritical hypothesis $(n-1)p&lt;1$, let $L_1=\max_i|C_i|$. Since $L_1^2\le\sum_i|C_i|^2$, Markov's inequality then gives, for every $r&gt;0$,</p>
      $$\mathbb P(L_1\ge r)\le
      \frac{n}{r^2[1-(n-1)p]}.$$
      <p>The estimate is useful when its right-hand side is small. It is an elementary bound, not a sharp description of the critical window.</p>

## The critical-window viewpoint {#section-window}

<a id="tag-F9EV" data-assertion="proposition" data-title="Erdős–Rényi critical-window component scale"></a><p>For Erdős–Rényi graphs, the classical <a href="#/criticality">critical window</a> is parametrised by</p>
      $$p=\frac1n+\lambda n^{-4/3},\qquad \lambda\in\mathbb R\text{ fixed},$$
      <p>with largest components on the $n^{2/3}$ scale as $n\to\infty$. This is a statement about a sequence of finite models and their component distributions. It cannot be expressed as the appearance of an actually infinite cluster in one finite graph.</p>
      <p>A precise scaling-limit theorem must specify its mode of convergence, ordering of components, and state space. The component scale alone does not determine the joint limiting law.</p>
<p><em>Idea of the proof.</em> Read precisely, the statement says that for fixed $\lambda$ and every fixed $j\ge1$ the size $L_j$ of the $j$-th largest component is of order $n^{2/3}$ in both directions: the sequences $n^{-2/3}L_j$ and $n^{2/3}/L_j$ are tight. Writing $p=(1+\lambda n^{-1/3})/n$ identifies the window with the one used for <a href="/articles/critical-random-graph-clusters/">critical Erdős–Rényi components</a>, and for $j=1$ the statement is the <a href="/tag/38XP/">two-sided tightness of the largest component</a>. Since $L_j\le L_1$, only the lower bound for $j\ge2$ needs a further argument. Count the vertices in components whose size lies between $n^{2/3}/A$ and $n^{2/3}$. By the <a href="/tag/Y0FX/">critical root-cluster tails</a> their expected number is at least of order $A^{1/2}n^{2/3}$, and the <a href="/tag/25Z4/">distinct-cluster comparison</a> bounds the variance by $O(A^{1/2}n^{4/3})$. Chebyshev's inequality then produces, with probability close to one, at least of order $A^{1/2}$ such components, hence at least $j$ of them once $A$ is large.</p>
:::details Proof
<p><em>Step 1 (setting and precise form).</em> Put $\theta=\lambda$, so that $p_n=1/n+\lambda n^{-4/3}=(1+\theta n^{-1/3})/n$; this lies in $[0,1]$ for all large $n$. For a vertex $v\in[n]$ write $C(v)$ for its component in $G(n,p_n)$. List the component sizes in decreasing order, with multiplicity, as $L_1\ge L_2\ge\cdots$, and set $L_j=0$ when there are fewer than $j$ components. The assertion proved is: for every integer $j\ge1$ and every $\varepsilon\in(0,1)$ there are $A&lt;\infty$ and $n_1$ such that</p>
      $$\mathbb P_{p_n}\bigl(A^{-1}n^{2/3}\le L_j\le An^{2/3}\bigr)\ge1-\varepsilon\qquad(n\ge n_1).$$
      <p>This is tightness of $n^{-2/3}L_j$ and of $n^{2/3}/L_j$ (with $1/0=\infty$). It contains the weaker reading in which $L_j=O_P(n^{2/3})$ and $L_j\ge cn^{2/3}$ with probability bounded below.</p>
<p><em>Step 2 (upper bound).</em> By the <a href="/tag/38XP/">tightness theorem for the largest component</a> there are $b_\theta&lt;\infty$ and $n_0(\theta)$ such that, for $n\ge n_0(\theta)$ and real $A\ge1$,</p>
      $$\mathbb P_{p_n}\bigl(L_1&gt;An^{2/3}\bigr)\le1-\mathbb P_{p_n}\bigl(A^{-1}n^{2/3}\le L_1\le An^{2/3}\bigr)\le\frac{b_\theta}{A}.$$
      <p>Since $L_j\le L_1$, the same bound holds for $\mathbb P_{p_n}(L_j&gt;An^{2/3})$. For $j=1$ the theorem itself also gives the lower bound, so assume $j\ge2$ from now on (the argument below works for $j=1$ as well).</p>
<p><em>Step 3 (root-cluster tails).</em> By the <a href="/tag/Y0FX/">critical-window root-cluster tails</a> there are a universal $C&lt;\infty$ and a threshold $n_2(\theta)$ such that, for $n\ge n_2(\theta)$ and every integer $k\ge1$,</p>
      $$\mathbb P_{p_n}(|C(1)|\ge k)\le C\bigl(\theta_+n^{-1/3}+k^{-1/2}\bigr),$$
      <p>and, taking $r=2$ there, constants $c=c(2,\theta)&gt;0$ and $n_3=n_0(2,\theta)$ such that $\mathbb P_{p_n}(|C(1)|\ge k)\ge ck^{-1/2}$ for $n\ge n_3$ and integers $1\le k\le2n^{2/3}$. A permutation of $[n]$ is an automorphism of $K_n$ and preserves the product law, so $|C(v)|$ has the law of $|C(1)|$ for every vertex $v$. Put $D_\theta=(\theta_++1)C$ and $c'=c/(2\sqrt2)$. From now on $n\ge\max(n_2(\theta),n_3)$.</p>
<p><em>Step 4 (a truncated count).</em> Let $2\le A\le n^{2/3}$, and put $a=n^{2/3}/A\ge1$, $k=\lceil a\rceil$ and $K=\lfloor n^{2/3}\rfloor$. Then $k&lt;a+1\le2a=2n^{2/3}/A\le n^{2/3}$, and since $k$ and $K$ are integers, $1\le k\le K$. With $w(s)=\mathbf 1_{\{k\le s\le K\}}$, set</p>
      $$Y=\sum_{v=1}^n w(|C(v)|)=\sum_{B}|B|\,w(|B|),$$
      <p>where the second sum runs over the components $B$, each counted once; the equality is the <a href="/tag/TUD2/">root-sum identity</a>. Each component with $w(|B|)=1$ contributes at most $K$ to $Y$, so at least $Y/K$ components have size in $[k,K]$. If $Y\ge jK$, at least $j$ components have size at least $k\ge a$, and then $L_j\ge a$. Hence</p>
      $$\{L_j&lt;a\}\subseteq\{Y&lt;jK\}.$$
<p><em>Step 5 (the mean).</em> By vertex symmetry, $\mu:=\mathbb E_{p_n}Y=n\mathbb P_{p_n}(|C(1)|\ge k)-\delta$ with $\delta:=n\mathbb P_{p_n}(|C(1)|\ge K+1)$. Since $k\le2n^{2/3}$, the lower tail gives</p>
      $$n\mathbb P_{p_n}(|C(1)|\ge k)\ge cn(2a)^{-1/2}=\frac c{\sqrt2}A^{1/2}n^{2/3}.$$
      <p>Since $K+1&gt;n^{2/3}$, the upper tail gives $0\le\delta\le Cn(\theta_+n^{-1/3}+n^{-1/3})=D_\theta n^{2/3}$. If $A\ge A_1:=8D_\theta^2/c^2$, then $D_\theta\le\frac c{2\sqrt2}A^{1/2}$, and therefore</p>
      $$\mu\ge\Bigl(\frac c{\sqrt2}A^{1/2}-D_\theta\Bigr)n^{2/3}\ge c'A^{1/2}n^{2/3}.$$
<p><em>Step 6 (the variance).</em> Expanding the square over components,</p>
      $$Y^2=\sum_B|B|^2w(|B|)+\sum_{B\ne B'}|B||B'|\,w(|B|)\,w(|B'|),$$
      <p>with the second sum over ordered pairs of distinct components. Let $F(s)=\mathbf 1_{\{s\ge k\}}$ on $[1,n]$; it is nonnegative and increasing, and $0\le w\le F$. Apply the <a href="/tag/25Z4/">distinct-cluster comparison</a> on $K_n$ with observation set $\Lambda=[n]$, whose cluster partition is the partition into components, and with $F=G$. Then $T_F=\sum_B|B|F(|B|)=Z_{\ge k}:=\sum_v\mathbf 1_{\{|C(v)|\ge k\}}$, and</p>
      $$\mathbb E_{p_n}\sum_{B\ne B'}|B||B'|\,w(|B|)\,w(|B'|)\le\mathbb E_{p_n}\sum_{B\ne B'}|B||B'|F(|B|)F(|B'|)\le\bigl(\mathbb E_{p_n}Z_{\ge k}\bigr)^2.$$
      <p>For the diagonal term, the root-sum identity and vertex symmetry give $\mathbb E_{p_n}\sum_B|B|^2w(|B|)=n\mathbb E_{p_n}[|C(1)|\,w(|C(1)|)]$. Since $s\,w(s)\le\min(s,K)=\sum_{i=1}^K\mathbf 1_{\{s\ge i\}}$ for every integer $s\ge1$, the upper tail, $K\le n^{2/3}$ and $\sum_{i=1}^Ki^{-1/2}\le2\sqrt K$ give</p>
      $$n\mathbb E_{p_n}[|C(1)|\,w(|C(1)|)]\le nC\sum_{i=1}^K\bigl(\theta_+n^{-1/3}+i^{-1/2}\bigr)\le nC\bigl(\theta_+n^{1/3}+2n^{1/3}\bigr)=(\theta_++2)Cn^{4/3}.$$
      <p>As $k\le K$, every vertex with $|C(v)|\ge k$ has either $|C(v)|\le K$ or $|C(v)|\ge K+1$, so $Z_{\ge k}=Y+Z_{\ge K+1}$ and $\mathbb E_{p_n}Z_{\ge k}=\mu+\delta$. Combining,</p>
      $$\operatorname{Var}_{p_n}(Y)=\mathbb E_{p_n}Y^2-\mu^2\le (\theta_++2)Cn^{4/3}+(\mu+\delta)^2-\mu^2=(\theta_++2)Cn^{4/3}+2\mu\delta+\delta^2.$$
<p><em>Step 7 (Chebyshev's inequality).</em> Suppose in addition that $A\ge(2j/c')^2$. Then $jK\le jn^{2/3}\le\frac{c'}2A^{1/2}n^{2/3}\le\mu/2$, so $Y&lt;jK$ forces $|Y-\mu|&gt;\mu/2$. By Steps 4–6, the bounds $\delta\le D_\theta n^{2/3}$ and $\mu\ge c'A^{1/2}n^{2/3}$, and $A^{-1}\le A^{-1/2}$,</p>
      $$\mathbb P_{p_n}(L_j&lt;a)\le\mathbb P_{p_n}(Y&lt;jK)\le\frac{4\operatorname{Var}_{p_n}(Y)}{\mu^2}
      \le\frac{4(\theta_++2)C}{c'^2A}+\frac{8D_\theta}{c'A^{1/2}}+\frac{4D_\theta^2}{c'^2A}\le\frac{b'_\theta}{A^{1/2}},$$
      <p>where $b'_\theta=4\bigl((\theta_++2)C+D_\theta^2\bigr)/c'^2+8D_\theta/c'$ does not depend on $j$, $A$ or $n$. Thus, with $A_0(\theta,j)=\max\{2,A_1,(2j/c')^2\}$, for all $n\ge\max(n_2(\theta),n_3)$ and all $A$ with $A_0(\theta,j)\le A\le n^{2/3}$,</p>
      $$\mathbb P_{p_n}\bigl(L_j&lt;A^{-1}n^{2/3}\bigr)\le\frac{b'_\theta}{A^{1/2}}.$$
<p><em>Step 8 (conclusion).</em> Given $\varepsilon\in(0,1)$, choose $A\ge A_0(\theta,j)$ with $b_\theta/A+b'_\theta A^{-1/2}\le\varepsilon$. For $n\ge n_1:=\max\bigl(n_0(\theta),n_2(\theta),n_3,\lceil A^{3/2}\rceil\bigr)$ one has $A\le n^{2/3}$, and Steps 2 and 7 give</p>
      $$\mathbb P_{p_n}\bigl(A^{-1}n^{2/3}\le L_j\le An^{2/3}\bigr)\ge1-\frac{b_\theta}A-\frac{b'_\theta}{A^{1/2}}\ge1-\varepsilon.$$
      <p>This is the assertion of Step 1.</p>
:::

## Exploration and other finite hosts {#section-connections}

<p><a href="#/exploration">Component exploration</a> turns a random graph into a queue process: discovering a vertex adds its previously unseen neighbours. The process suggests branching approximations in sparse regimes and a different scaling analysis near the critical window.</p>
      <p>Finite tori and hypercubes also have critical-window questions, but their geometry and dependence between explored connections require their own estimates. The component-moment identity and <a href="#/universal-tightness">universal maximum-cluster bounds</a> still apply to these finite hosts. Their critical parameters and window widths remain model-specific.</p>
