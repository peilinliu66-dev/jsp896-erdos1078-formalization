# JSP-000896 / Erdős 1078: the exact multipartite threshold

This note gives the finite mathematical argument implemented by the local Lean source. It includes sufficiency and actual extremal graphs for every number of parts and every positive part size, followed by both original asymptotic regimes. Build results and the final axiom checks are recorded separately in the verification evidence.

The mathematical problem originates in Bollobás–Erdős–Szemerédi [1]. The known even-part threshold and the all-size sharpness construction are described by Szabó–Tardos [2]; the odd-part threshold is due to Haxell–Szabó [3]. The local formalization develops the finite certificate and switching proofs, the explicit constructions, the integer adapters, and the limit arguments.

## 1. Statement and literal graph model

Fix integers $r\ge2$ and $n\ge1$. The vertex set is

$$
 V=\{0,\ldots,r-1\}\times\{0,\ldots,n-1\},
 \qquad V_i=\{i\}\times\{0,\ldots,n-1\}.
$$

A graph is an ordinary simple graph on all of $V$, with no edges inside a class $V_i$. Its degree is the cardinality of its actual neighbor set. A transversal is a function $f:\{0,\ldots,r-1\}\to\{0,\ldots,n-1\}$, selecting $(i,f(i))$ from each class. It is independent if all the selected vertices are pairwise nonadjacent, and a clique if vertices from distinct classes are adjacent.

Put

$$
 s=\left\lfloor\frac r2\right\rfloor,
 \qquad D(r,n)=\left\lceil\frac{sn}{2s-1}\right\rceil,
 \qquad T(r,n)=(r-1)n-D(r,n).
 \tag{1}
$$

The independent-transversal theorem consists of both assertions:

1. Every such graph $H$ with maximum degree strictly below $D(r,n)$ has an independent transversal.
2. There exists such a graph $H$ with maximum degree at most $D(r,n)$ and no independent transversal.

Equivalently, in the original clique formulation:

1. Every such graph $G$ whose every vertex has degree strictly above $T(r,n)$ has a transversal clique.
2. There exists such a graph $G$ whose every vertex has degree at least $T(r,n)$ and which has no transversal clique.

Together these assertions identify the exact threshold, including the equality case. There is no divisibility restriction on $n$, and no extra certificate or structural hypothesis in the final theorem.

The cross-part complement is defined by

$$
 u\sim_{\overline G}v
 \quad\Longleftrightarrow\quad
 \operatorname{class}(u)\ne\operatorname{class}(v)
 \ \text{ and }\ u\not\sim_Gv.
$$

Every vertex has exactly $(r-1)n$ potential neighbors outside its own class, so

$$
 \deg_G(v)+\deg_{\overline G}(v)=(r-1)n. \tag{2}
$$

A transversal clique in $G$ is precisely an independent transversal in $\overline G$. Thus it suffices to prove the independent assertions and apply (2). The source defines the graph and degree functions in `JSP896/Statement.lean`, and proves the degree identity and the sign conversions in `Complement.lean` and `ThresholdArithmetic.lean`.

## 2. A finite domination certificate

This section works for any finite graph whose vertex set is partitioned into nonempty independent classes; the classes need not have equal sizes. A partial independent transversal is an independent set using at most one vertex per class. A maximum partial transversal exists by maximizing cardinality over the finite collection of all subsets of the vertex set.

Suppose no full independent transversal exists. We construct a nonempty set $I$, a maximum partial transversal $T$, and a set $S$ of active classes, with the following properties:

- $S$ is exactly the set of classes met by $I$.
- The graph induced by $I$ is a disjoint union of nontrivial stars, with centers $I\setminus T$ and leaves $I\cap T$.
- Each center has in $I$ all of its neighbors in $T$, and every leaf has exactly one center as its neighbor.
- On contracting the active classes, the star edges give a tree on $S$. Different actual edges do not collapse to the same ordered pair of classes.
- $I$ dominates every vertex in the union of the classes in $S$: each such vertex has a neighbor in $I$.

The faithful-edge condition matters: acyclicity of a simple class graph alone would discard parallel-edge information. It is retained explicitly in the Lean invariant.

### 2.1 Construction by feasible extensions

Call $(I,T)$ feasible if it has the star and class-tree invariants above, excluding the domination conclusion, and also satisfies two compatibility conditions. First, the active classes represented by $T$ are represented by $I\cap T$. Second, no one center's star can be made smaller by changing $T$ on the same represented classes, avoiding all centers, and leaving every other center's star unchanged. This last condition is a local minimality condition. The empty pair $(\varnothing,T)$ is feasible for any maximum $T$.

For a feasible pair, a compatible partial transversal $U$ represents exactly the classes of $T$, avoids the centers, and preserves each existing center's complete star as a set. Such a $U$ is still maximum. The agreement condition forces $U$ and $T$ to agree on every active class.

If $I$ is empty, choose a vertex $w$ in a class missing from $T$. If $I$ is nonempty and does not dominate all its active classes, choose an undominated vertex $w$ in an active class. In either case, among the finitely many compatible $U$, choose one minimizing the new star

$$
 C(w,U)=\{w\}\cup(N(w)\cap U).
$$

This star is nontrivial. In the first case, a vertex with no neighbor in $U$ could be appended to $U$, contradicting maximal cardinality. In the second case, suppose $w$ has no neighbor in $U$. Let $u$ be the representative in $U$ of the active class of $w$. It is an old leaf with a unique old center $z$. Replacing $u$ by $w$ preserves independence, the represented classes, and all centers except $z$; it removes $u$ from $z$'s star. This contradicts the local minimality of the old feasible pair.

Every new leaf belongs to a previously inactive class: otherwise compatibility and agreement would put it in $I$, contradicting that $w$ is undominated by $I$. Hence adding $C(w,U)$ attaches genuinely new leaf classes to the class tree, preserves acyclicity and faithfulness, and preserves the star forest. Local minimality for old centers follows from their old invariant; for the new center it follows from the choice of $U$. Thus

$$
 (I\cup C(w,U),U)
$$

is feasible and has a strictly larger first set.

Choose a feasible extension with maximum $|I|$. The extension step proves that it is nonempty and dominates all its active classes. Starting from a nonempty feasible seed also preserves every seed vertex and the representatives of its initially active classes. The source obtains maximality by a finite maximum, so no unproved termination or augmentation principle is used.

### 2.2 Size and weighted information

Write $q=|S|$. Nonemptiness and the absence of isolated vertices in $I$ imply $q\ge2$. Each actual star edge gives a different edge of the class tree, so there are $q-1$ actual edges. Every vertex of $I$ lies on an edge, giving

$$
 |I|\le2q-2. \tag{3}
$$

If all active classes have size $n$ and every graph degree is at most $d$, domination gives

$$
 qn\le\sum_{v\in I}\deg(v)\le|I|d\le(2q-2)d. \tag{4}
$$

We will also use information stronger than (3). For any certificate constructed in a graph with classes indexed by a fixed-point-free involution $i\mapsto i^*$, and no edges between opposite classes, put

$$
 t_i=|I\cap V_i|.
$$

Each certificate vertex has a neighbor in the certificate. Choosing one such neighbor injects the certificate vertices of $V_i$ into their possible neighboring classes: the faithful-edge invariant prevents two vertices from producing the same ordered class pair. Consequently,

$$
 t_i\le q-1-\mathbf1_{\{i^*\in S\}}. \tag{5}
$$

The possible classes exclude $i$, and also exclude $i^*$ when the latter is selected. This is the multiplicity estimate needed below.

The complete certificate construction is implemented in `FiniteTransversal.lean`, `FeasiblePair.lean`, the extension modules, `DominationCertificate.lean`, `CertificateSize.lean`, and `CertificateMultiplicity.lean`.

## 3. Even-part sufficiency and the induced matching certificate

For an even number $r=2s$, suppose $(2s-1)d<sn$. If there were no full independent transversal, (4) would hold for some $2\le q\le r$. Since $x/(2x-2)$ decreases for $x>1$,

$$
 d\ge\frac{qn}{2q-2}\ge\frac{rn}{2r-2}
   =\frac{sn}{2s-1},
$$

contradicting the strict inequality. This proves even-part sufficiency.

For the odd proof, and for the cell constructions, we need a more precise certificate. Suppose $r\ge3$ and

$$
 (2r-4)d<(r-1)n. \tag{6}
$$

Every nonempty dominating feasible certificate uses all $r$ classes. Otherwise $q\le r-1$ in (4), and

$$
 d\ge\frac{qn}{2q-2}\ge\frac{(r-1)n}{2r-4},
$$

contradicting (6).

Its induced star forest is in fact a perfect matching. To see this, let $C=I\setminus T$ and $L=I\cap T$. Each center has a leaf and leaves have unique centers, so $|C|\le|L|$. If these cardinalities are equal, each center has exactly one leaf and every vertex has exactly one neighbor inside $I$. Otherwise

$$
 |I|=|C|+|L|\le2|T|-1\le2r-3.
$$

But (6) implies $(2r-3)d<rn$: indeed

$$
 \frac{r-1}{2r-4}\le\frac r{2r-3}
 \quad\text{because}\quad
 r(2r-4)-(r-1)(2r-3)=r-3\ge0.
$$

The latter bound contradicts domination of all $rn$ vertices by $I$. Thus $I$ is an **induced matching configuration**, abbreviated IMC: a perfect induced matching whose faithful class graph is a tree on all $r$ classes. In particular,

$$
 |I|=2r-2. \tag{7}
$$

Any IMC in a no-transversal graph dominates every vertex, whether or not it was produced by the certificate construction. Root its class tree at the class of a vertex $v$. From each other class choose the matching endpoint whose partner is in the parent class. These choices form an independent partial transversal missing just the root class. If $v$ were undominated by the IMC, adjoining $v$ would give a full independent transversal.

This gives the endpoints `FeasiblePair.exists_matching_configuration` and `MatchingConfiguration.Tree.dominates`.

## 4. Every critical edge belongs to an IMC

Choose an edge-minimal spanning subgraph $H$ of a hypothetical no-transversal graph: $H$ has no full independent transversal, but deleting any edge produces one. Such a graph exists by minimizing the finite number of edges among the no-transversal spanning subgraphs. Taking a subgraph preserves all upper degree bounds and the prescribed vertex classes.

Let $ab$ be an edge of $H$, and let $U$ be a full independent transversal after deleting $ab$. Both $a$ and $b$ lie in $U$; otherwise $U$ would already be independent in $H$. The set $T=U\setminus\{a\}$ has $r-1$ vertices and is maximum in $H$. The pair

$$
 (\{a,b\},T)
$$

is feasible. Its sole center $a$ has exactly the leaf $b$ in $T$, its class graph is the single edge, and local minimality follows because a vertex in the missing class must have a neighbor in every maximum partial transversal on these $r-1$ classes. Extend this seed by Section 2. Under (6), Section 3 turns the extended certificate into a full IMC still containing $a,b$.

Thus every edge of an edge-minimal no-transversal graph lies in an actual IMC. This is `CriticalEdge.every_edge_in_matching`. The eventual contradiction is proved in $H$ itself; no independent set of $H$ is transferred back to the denser original graph.

## 5. The paired-cell structure argument for all $r\ge5$

Continue with an edge-minimal no-transversal graph satisfying (6), with $r\ge5$, and fix an IMC $I$. Index its endpoints by $i\in I$, and let $i^*$ be the unique matching partner of $i$. Define the literal unique-neighbor cell

$$
 A_i=\{v:N(v)\cap I=\{i\}\}.
$$

The cells are disjoint, nonempty because $i^*\in A_i$, and satisfy $|A_i|\le\deg(i)\le d$. Their union is the core; vertices outside it have at least two neighbors in $I$, because $I$ dominates the graph.

### 5.1 Opposite cells and actual exchanges

Delete the matching pair $i,i^*$. The class tree splits into two components. A vertex of $A_i$ lies on the class-tree side containing $i^*$. Otherwise, orient the two components toward its class and the class of $i^*$. The remaining matching endpoints give an independent partial transversal missing those two classes; the cell vertex and $i^*$ are nonadjacent and avoid all remaining endpoints, so adjoining them would give a full transversal.

It follows that every vertex of $A_i$ is adjacent to every vertex of $A_{i^*}$. A nonadjacent pair would lie on the two opposite tree-cut sides and could be adjoined to the corresponding two-root partial transversal.

Replacing $i,i^*$ by any chosen pair from $A_i,A_{i^*}$ therefore gives another IMC: the pair is an edge, has no other neighbors among the remaining endpoints, and joins the two class-tree components. All tree and faithful-edge conditions are preserved.

More generally, suppose one chooses $f(i)\in A_i$ for every endpoint and the only edges among the choices are the opposite pairs. Replace one coordinate at a time, retaining the current choice on the other endpoint of that pair. The unique-neighbor and prescribed-edge conditions prove each intermediate exchange valid. The final set of choices is an actual full IMC. These are the one-pair and simultaneous exchanges in `MatchingExchange.lean`.

### 5.2 Total deficit below one degree budget

Write

$$
 a_i=|A_i|,\qquad \delta_i=d-a_i,\qquad
 \Delta=\sum_{i\in I}\delta_i.
$$

Let $m(v)=|N(v)\cap I|$. Then $m(v)=1$ on the core and $m(v)\ge2$ elsewhere. Counting incidences gives

$$
 \sum_v m(v)=\sum_{i\in I}\deg(i)\le(2r-2)d,
$$

and hence

$$
 \sum_i a_i\ge2rn-(2r-2)d,
 \qquad
 \Delta\le(4r-4)d-2rn. \tag{8}
$$

For every $r\ge5$, (6) implies

$$
 (4r-5)d<2rn. \tag{9}
$$

The required coefficient comparison is

$$
 2r(2r-4)-(r-1)(4r-5)=r-5\ge0.
$$

Combining (8) and (9) yields

$$
 \Delta<d. \tag{10}
$$

The strict inequality remains valid at $r=5$; the coefficient comparison becomes equality, while (6) is strict. Thus this route treats $r=5$ together with all larger odd cases.

### 5.3 The residual-cell independent transversal lemma

Consider a family of disjoint nonempty cells in a host graph of maximum degree at most $d$, with opposite complete bipartite pairs, sizes $a_i\le d$, and total deficit (10). Remove sets $R_i\subseteq A_i$ satisfying

$$
 \sum_i|R_i|\le d,
$$

and assume every residual cell remains nonempty. On the actual residual vertices define an auxiliary graph by retaining the original edges between distinct, nonopposite cells. A vertex in cell $i$ has auxiliary degree at most $\delta_{i^*}$: its original degree is at most $d$, and all $a_{i^*}$ opposite-cell neighbors have been excluded.

This auxiliary graph has an independent transversal. Suppose otherwise and construct its genuine domination certificate by Section 2. Let $S$ be its $q\ge2$ active cells and $t_i$ the number of certificate vertices in cell $i$. Domination and the residual sizes give

$$
 qd-\sum_{i\in S}\delta_i-\sum_{i\in S}|R_i|
 \le\sum_{i\in S}t_i\delta_{i^*}.
$$

Using the deletion bound,

$$
 (q-1)d
 \le\sum_{i\in S}\delta_i+\sum_{i\in S}t_i\delta_{i^*}. \tag{11}
$$

Reindex the second sum by the involution. The coefficient of $\delta_j$ on the right is

$$
 \mathbf1_{\{j\in S\}}+
   \mathbf1_{\{j^*\in S\}}t_{j^*}\le q-1,
$$

by (5). The four membership possibilities for $j,j^*$ give respectively coefficients at most $q-1,1,q-1,0$. Therefore (11) implies

$$
 (q-1)d\le(q-1)\Delta<(q-1)d,
$$

a contradiction.

The auxiliary transversal selects one vertex from every old cell with no edges between nonopposite cells. Opposite selected vertices are adjacent by completeness, so Section 5.1 converts these actual choices into a replacement IMC. This entire construction, including the residual vertex type and its degree bound, is in `PairedCellTransversal.lean` and `CellDeletion.lean`.

### 5.4 Completing and partitioning the expanded cells

Every graph vertex $v$ is complete to at least one old cell. If it were complete to none, delete $N(v)\cap A_i$ from each cell. Every cell remains nonempty, and the total deletion is at most $\deg(v)\le d$. Section 5.3 produces a replacement IMC avoiding $N(v)$, which does not dominate $v$, contrary to Section 3.

The complete cell is unique. For $i\ne j$, (10) gives

$$
 a_i+a_j=2d-\delta_i-\delta_j>d.
$$

A vertex of degree at most $d$ cannot be complete to both disjoint cells. Define

$$
 B_i=\{v:v\text{ is complete to }A_{i^*}\}.
$$

These expanded cells partition the whole vertex set and contain their corresponding old cells, $A_i\subseteq B_i$.

Opposite expanded cells are also complete. Take $a\in B_i$, $b\in B_{i^*}$. Make all deletions at once in the old cells, using the set

$$
 U=(N(a)\setminus A_{i^*})\cup(N(b)\setminus A_i),
 \qquad R_j=A_j\cap U.
$$

The total number removed is at most

$$
 |U|\le(d-a_{i^*})+(d-a_i)
        =\delta_i+\delta_{i^*}<d.
$$

All residual cells are nonempty. In $A_i$ the removal comes only from the first term of $U$, of size at most $\delta_{i^*}<a_i$; the symmetric bound applies in $A_{i^*}$. For $j\notin\{i,i^*\}$,

$$
 |R_j|\le\delta_i+\delta_{i^*}
    <d-\delta_j=a_j,
$$

since $\delta_i+\delta_{i^*}+\delta_j\le\Delta<d$.

The residual-cell lemma now yields a replacement IMC $J$. In $J$, $a$ has as its only neighbor the selected representative of $A_{i^*}$, and $b$ has as its only neighbor the selected representative of $A_i$. Those representatives are matching partners. Opposite-cell completeness for $J$ therefore gives $a\sim b$. Thus the original expanded cells form complete opposite pairs.

### 5.5 Excluding all extra edges

Each expanded cell has size at most $d$, because any vertex in the nonempty opposite cell is adjacent to all of it. As the $2r-2$ expanded cells partition $rn$ vertices,

$$
 |B_i|\ge rn-(2r-3)d. \tag{12}
$$

For any full IMC $J$, the number $E_J$ of vertices with at least two neighbors in $J$ is at most

$$
 E_J\le(2r-2)d-rn. \tag{13}
$$

Indeed every vertex has at least one neighbor in $J$, and each multiply dominated vertex contributes at least one further incidence. Inequality (9) makes the lower bound in (12) strictly larger than the upper bound in (13).

Consequently $J$ contains at most one vertex from each expanded cell: two vertices of $J$ in $B_i$ would multiply dominate every vertex of $B_{i^*}$, contradicting (12)–(13). It has $2r-2$ vertices and there are $2r-2$ expanded cells, so it contains exactly one in every cell. Its matching edges must be the opposite-cell pairs, since those representatives are already adjacent and $J$ induces a perfect matching.

Every graph edge belongs to an IMC by Section 4. Hence every edge joins opposite expanded cells. Together with the proved opposite completeness, this shows that the graph is a disjoint union of $r-1$ complete bipartite components. This is the actual model constructed by `CellStructure.lean`; its fields give a unique distinguished neighbor in $I$ for every vertex and the exact adjacency equivalence.

## 6. Odd-part sufficiency through a finite terminal dominator block

Let $r=2t+1\ge5$, and suppose

$$
 (2t-1)d<tn. \tag{14}
$$

In a hypothetical no-transversal graph, take an edge-minimal spanning subgraph as in Section 4. Condition (14) is exactly (6) for $r=2t+1$. Section 5 supplies a full IMC and its disjoint complete-bipartite model. We now obtain a contradiction entirely within that subgraph.

### 6.1 Centroid and the actual rooted orientation

The IMC class graph is a tree on $2t+1$ classes. Choose a class $o$ minimizing the sum of its distances to all classes. Moving from $o$ across an edge into a branch containing $h$ classes changes that distance sum by

$$
 (2t+1)-2h.
$$

Minimality forces $h\le t$. Therefore every nonroot descendant set lies in a branch of size at most $t$.

For each class $c\ne o$, let $b_c$ be the matching endpoint in class $c$ whose matching partner lies in its parent class, and write $w_c$ for that partner. Call them black and white, respectively. The black endpoints form an independent partial transversal missing $o$, and every matching endpoint is one of these black or white endpoints.

Let $\operatorname{ind}(v)$ denote the unique neighbor of $v$ in the IMC. The exact bipartite model has adjacency rule

$$
 v\sim u
 \quad\Longleftrightarrow\quad
 \operatorname{ind}(u)=\operatorname{ind}(v)^*. \tag{15}
$$

In particular, $\operatorname{ind}(b_c)=w_c$ and $\operatorname{ind}(w_c)=b_c$.

### 6.2 An auxiliary digraph and two proved switches

Define an arc $x\to y$, where $y\ne o$, if some vertex in class $x$ has distinguished neighbor $b_y$. Every outward parent edge is an arc, witnessed by $w_y$. Thus $o$ reaches every class.

For a set $S$ of classes, define the independent covering set

$$
 Q(S)=\{v:\operatorname{ind}(v)=b_c
                 \text{ for some }c\in S\setminus\{o\}\}
       \ \cup\ \{b_c:c\notin S,\ c\ne o\}.
 \tag{16}
$$

Its first part uses the white sides of components indexed by $S$, while the retained black endpoints use the remaining components. Equation (15) proves independence.

**Closed switch.** If $o\in S$ and every class $x\in S$ has an arc to a class in $S$, arc witnesses show that $Q(S)$ meets every class in $S$. Retained black endpoints cover all other classes. Choosing one vertex from each covered class gives a full independent transversal.

In particular, an arc $x\to y$ together with a directed route $y\leadsto x$ yields such a switch. Take $S=\{z:z\leadsto x\}$. The root belongs to $S$; $x$ uses the specified arc, and every other class in $S$ has a first step toward $x$. Thus under the no-transversal assumption the digraph has no directed cycle, including a loop, and reachability is antisymmetric.

**Avoiding-path switch.** Suppose $v\in V_x$ has $\operatorname{ind}(v)=w_c$, and a route from $o$ to $x$ avoids $c$. Let $S$ be the classes admitting a route to $x$ that avoids $c$, with endpoints included in the avoidance condition. Then $o\in S$, $c\notin S$, and every $z\in S\setminus\{x\}$ has an arc inside $S$. The set $Q(S)\cup\{v\}$ is independent: $v$ lies on the black side of component $c$, whose white side does not occur in $Q(S)$. It covers $x$, all other classes of $S$, and all classes outside $S$, so it gives a full independent transversal.

Consequently, under the no-transversal assumption,

$$
 \operatorname{ind}(v)=w_c
 \quad\Longrightarrow\quad
 \text{every route from }o\text{ to class}(v)\text{ contains }c.
 \tag{17}
$$

These are actual independent sets and finite choices, implemented in `OddComponentsSwitching.lean`.

### 6.3 Finite dominators and a terminal block

Say that a class $c$ dominates a class $x$ in the digraph if every route from $o$ to $x$ contains $c$. Dominance is reflexive and transitive; a nonroot class does not dominate $o$. Because $o$ reaches $x$, domination of $x$ by $c$ also supplies a route $c\leadsto x$.

Two dominators $c,d$ of the same class $x$ are comparable by dominance. If $c$ does not dominate $d$, choose an $o$-to-$d$ route avoiding $c$. A $d$-to-$x$ route must then reach $c$. For $c\ne d$, acyclicity excludes $c\leadsto d$, so a $c$-to-$x$ route avoids $d$. If an $o$-to-$c$ route also avoided $d$, concatenation would contradict that $d$ dominates $x$. Thus $d$ dominates $c$.

A root dominator is a nonroot class with no distinct nonroot dominator of its own. Every nonroot $x$ has a unique root dominator. To prove existence by a finite choice, put

$$
 f(c)=|\{y:c\leadsto y\}|.
$$

If $c\leadsto d\ne c$, acyclicity gives $f(d)<f(c)$: the future of $d$ is a proper subset of the future of $c$. Among the nonroot dominators of $x$, choose one with maximum $f$. A distinct nonroot dominator of that choice would have still larger $f$, a contradiction. Comparability gives uniqueness.

Choose a root dominator $c$ with minimum $f(c)$, and put

$$
 L=\{x:c\text{ dominates }x\}.
$$

The set $L$ contains $c$ and omits $o$. It has two closure properties:

1. If $x\in L$ and $x\to y$, then $y\in L$. An arc to the root would create a cycle. Otherwise let $e$ be the root dominator of $y$. If $y\ne e$, every route from $o$ to $x$ must already contain $e$, since appending $x\to y$ cannot first introduce $e\ne y$. The root dominators of $x$ are therefore both $c$ and $e$, so $c=e$ and $y\in L$. If $y=e\notin L$, then $c\leadsto x\to e\ne c$, giving $f(e)<f(c)$, contrary to the minimal choice of $c$.
2. If $x\in L$ and a nonroot $d$ dominates $x$, then $d\in L$. Comparability says either $c$ dominates $d$, or $d$ dominates $c$. In the latter case root-domination forces $d=c$.

Every parent-tree route is also an auxiliary-digraph route. Thus $c$ lies on the parent route from $o$ to every $x\in L$. It follows that $L$ is contained in the parent-descendant set of $c$. By the centroid,

$$
 1\le\ell:=|L|\le t. \tag{18}
$$

### 6.4 A missing endpoint gives the contradiction

Take any vertex $v$ in a class of $L$. If $\operatorname{ind}(v)=b_d$, the arc from its class to $d$ and the first closure property give $d\in L$. If $\operatorname{ind}(v)=w_d$, (17) and the second closure property give $d\in L$.

The distinguished neighbor cannot be $b_c$: the resulting arc from $\operatorname{class}(v)$ to $c$, together with domination's route $c\leadsto\operatorname{class}(v)$, would trigger the closed switch. Therefore the actual set

$$
 Z=\bigl(\{b_d:d\in L\}\cup\{w_d:d\in L\}\bigr)
                      \setminus\{b_c\}
$$

dominates all vertices in the classes of $L$, and $|Z|\le2\ell-1$. Its domination count gives

$$
 \ell n\le|Z|d\le(2\ell-1)d. \tag{19}
$$

But (14) and (18) imply $(2\ell-1)d<\ell n$. Indeed,

$$
 t(2\ell-1)\le\ell(2t-1)
$$

because $\ell\le t$, and multiplying (14) by $\ell$ gives

$$
 t(2\ell-1)d\le\ell(2t-1)d<\ell tn.
$$

Divide by $t>0$. This contradicts (19), establishing the odd-part sufficiency theorem. The source endpoint is `OddComponents.hasFull_of_odd_components`, assembled in `independentTransversal_of_odd_bound`.

## 7. The two and three class cases

For $r=2$ and $r=3$, formula (1) gives $D=n$.

For $r=2$, fix a vertex in one nonempty class. Its degree below $n$ leaves a nonneighbor in the other class; the two vertices give an independent transversal.

For $r=3$, pass to the cross-part complement $G$, where every vertex has degree strictly greater than $n$. Orient class pairs cyclically $A\to B\to C\to A$. Choose a vertex $v$ with maximum forward degree $M\le n$, and relabel cyclically so $v\in A$. Since its total degree exceeds $n$, it has a neighbor $w\in C$. Vertex $w$ has forward degree, toward $A$, at most $M$. Therefore its backward degree, toward $B$, is greater than $n-M$. The $M$ neighbors of $v$ in $B$ and the more than $n-M$ neighbors of $w$ in $B$ intersect. A vertex in their intersection completes a triangle using all three classes. Complementation gives the desired independent transversal.

Both arguments require $n>0$, exactly as in the original quantified statement. `SmallCases.lean` constructs the selected vertices and the resulting transversal function.

## 8. Actual sharpness graphs for every positive $n$

Let $k\ge1$, $n,d\ge1$, with

$$
 kn\le(2k-1)d. \tag{20}
$$

We construct a graph on $2k$ independent classes of size $n$, with maximum degree at most $d$, and no independent transversal. The construction follows Szabó–Tardos [2, Construction 3.3], encoded with literal component, side, and position labels.

### 8.1 The branch $n\le d$

Use one $K_{n,n}$, with its two sides as the first two classes, and $2k-2$ isolated classes of size $n$. All degrees are at most $n\le d$. Every full transversal selects one vertex from each side of the $K_{n,n}$ and contains an edge.

### 8.2 Positive remainder parameters

Assume $d<n$, and set

$$
 i=2d-n,\qquad
 a=n-d=d-i,\qquad
 q=\left\lfloor\frac{d-1}{i}\right\rfloor,\qquad
 u=d-qi.
 \tag{21}
$$

Condition (20) gives $ki\ge d>0$, so $i\ge1$. Since $d<n$, $a>0$ and $i<d$. The division of $d-1$ by $i$ gives

$$
 1\le q\le k-1,\qquad 1\le u\le i,
 \qquad d=qi+u,
$$

and hence

$$
 a=(q-1)i+u\le qi,
 \qquad n=d+a=2d-i.
 \tag{22}
$$

The positive remainder convention includes the divisible case: when $i\mid d$, it gives $u=i$ and $q=d/i-1$. Equivalently,

$$
 q=\left\lceil\frac{d-i}{i}\right\rceil,
$$

the convention used in Construction 3.3. No residue class of $n$ is omitted.

### 8.3 The two forced chains

Take $2q+1$ disjoint complete bipartite components with sides $A_j,B_j$, indexed by $0\le j\le2q$. All noncentral sides have size $d$; the two central sides $A_q,B_q$ have size $a+u\le d$.

For the left half, take $q$ chain classes

$$
 A_j\cup B'_{j+1}\qquad(0\le j<q),
$$

where $|B'_{j+1}|=a$. The leftover class consists of $B_0$ together with the remaining vertices of $B_1,\ldots,B_q$. Its size is

$$
 d+(q-1)i+u=d+a=n.
$$

Each chain class has size $d+a=n$. Reflect the same arrangement on the right, reversing $A$ and $B$. Its leftover class starts with $A_{2q}$, and the reversed chain ends at $A_q$. This gives $2(q+1)$ independent classes of size $n$. A class combines sides of consecutive components or uses only one side label, so it never contains opposite sides of a common component.

Every independent transversal meets the central $B_q$ side. Its left leftover class selects some $B_j$, $0\le j\le q$. If $j<q$, independence excludes $A_j$; the representative from the chain class $A_j\cup B'_{j+1}$ must then lie in $B_{j+1}$. Induction reaches $B_q$. The reflected chain forces a vertex in $A_q$. These two selected vertices are adjacent, a contradiction.

If $q<k-1$, append $2(k-q-1)$ isolated classes of size $n$. Any full independent transversal would restrict to one in the two-chain graph, which is impossible. Every component side has size at most $d$, so every degree is at most $d$.

### 8.4 Literal finite encoding and boundary preservation

The source does not assume the existence of a graph realizing the description. A left half-class $j\in\{0,\ldots,q\}$ has actual positions $x\in\{0,\ldots,n-1\}$. For $j<q$, positions $x<d$ are on $A_j$ with component-side position $x$; positions $x\ge d$ are on $B_{j+1}$ with position $x-d<a$.

In leftover class $q$, positions $x<d$ lie on $B_0$. For $x\ge d$, put $h=x-d$ and use

$$
 \text{component}=1+\left\lfloor\frac hi\right\rfloor,
 \qquad \text{side}=B,
 \qquad \text{position}=a+(h\bmod i).
$$

The bound $a\le qi$ keeps the component at most $q$. The position intervals $[0,a)$ and $[a,d)$ separate chain vertices from leftover packets. The last packet has the positive size $u$. The right half reflects component $c$ to $2q-c$ and reverses the side label. The two halves overlap only at component $q$, on opposite sides.

The component/side/position map is injective. Define adjacency to mean equal component labels and opposite Boolean side labels. Distinct neighbors inject into their positions on the opposite side, all below $d$, proving the actual degree bound. The same-class label check proves partiteness. The forcing induction described above proves the obstruction for the actual graph. Finally the finite class type is enumerated by $\operatorname{Fin}(2k)$.

For $r=2k+1$, append one isolated $n$-vertex class. Restriction again preserves the obstruction. Taking $k=\lfloor r/2\rfloor$ and $d=D(r,n)$ satisfies (20) by the ceiling property. Thus the witness exists for every $r\ge2,n\ge1$, including $n=1$. This is `exists_independent_sharpness_at_threshold`. Cross-part complementation gives `exists_sharpness_at_threshold` in the original clique formulation.

## 9. Exact integer assembly and the original limits

For integers $s\ge1$, $n,d\ge0$,

$$
 d<\left\lceil\frac{sn}{2s-1}\right\rceil
 \quad\Longleftrightarrow\quad (2s-1)d<sn. \tag{23}
$$

For $n>0$, $1\le D(r,n)\le n\le(r-1)n$. This also justifies every natural subtraction appearing in the complement adapters. Sections 3, 6, and 7 apply to the bound $d=D(r,n)-1$, which bounds every degree strictly below $D(r,n)$. Section 8 supplies the actual equality witness. Equations (2) and (23) assemble the literal `FullResolution` theorem.

For a fixed $r\ge2$, write

$$
 \alpha_r=\frac{s}{2s-1},\qquad c_r=(r-1)-\alpha_r.
$$

The ceiling sandwich gives, for $n>0$,

$$
 \alpha_r\le\frac{D(r,n)}n\le\alpha_r+\frac1n.
$$

The squeeze theorem yields

$$
 \lim_{n\to\infty}\frac{D(r,n)}n=\alpha_r,
 \qquad
 \lim_{n\to\infty}\frac{T(r,n)}n=c_r. \tag{24}
$$

These limits concern the true extremal thresholds because the full finite sufficiency and sharpness statements have already been proved.

As $r\to\infty$, $s=\lfloor r/2\rfloor\to\infty$, and

$$
 \frac{s}{2s-1}=\frac12+\frac{1}{2(2s-1)}\longrightarrow\frac12.
$$

Therefore

$$
 (r-1)-c_r\longrightarrow\frac12,
 \qquad
 c_r-(r-2)=1-\bigl((r-1)-c_r\bigr)\longrightarrow\frac12. \tag{25}
$$

The second expression is the large-$r$ clique-coefficient form in the original Bollobás–Erdős–Szemerédi paper. The source also exports the independent coefficient and the equivalent clique deficit form. `ThresholdAsymptotics.lean` proves the fixed-$r$ and large-$r$ limits; `Main.lean` assembles them with the unconditional finite resolution in `full_resolution_with_original_limits`.

## 10. Formal endpoint and verification evidence

The local Lean proof uses actual finite graphs, finite sets, adjacency, and transversal functions throughout. Finite certificate maxima, edge minimization, replacements, residual auxiliary graphs, centroid selection, both switches, and all extremal witnesses are constructed in the dependency chain. The full-resolution theorem takes only the original $r,n$ parameters and the stated graph hypotheses.

The principal exports are:

- `JSP896.independentTransversal_of_degree_lt_threshold`
- `JSP896.transversalClique_of_degree_gt_threshold`
- `JSP896.exists_independent_sharpness_at_threshold`
- `JSP896.exists_sharpness_at_threshold`
- `JSP896.full_resolution`
- `JSP896.full_resolution_with_original_limits`

`SOURCE_MAP.md` identifies the source file for each proof stage. The pinned environment is Lean `leanprover/lean4:v4.35.0-rc3` and Mathlib revision `2a885768dae569d938bb9ff3474da6a8753bb90a`, with the complete dependency lock in `lake-manifest.json`. Actual compiler outputs, source-bound run records, final theorem expansion, and transitive axiom checks form the separate verification evidence.

## References

1. B. Bollobás, P. Erdős, E. Szemerédi, *On complete subgraphs of r-chromatic graphs*, Discrete Mathematics 13 (1975), 97–107. [Original paper](https://users.renyi.hu/~p_erdos/1975-19.pdf). The original threshold and coefficient questions are in the introduction; the tripartite case is discussed in Section 2.
2. T. Szabó, G. Tardos, *Extremal problems for transversals in graphs with bounded degree*, Combinatorica 26 (2006), 333–351. [Author manuscript](https://www.renyi.hu/~tardos/tibortransversal.pdf). Construction 3.3 and Corollary 3.6 appear on manuscript pages 12–13.
3. P. Haxell, T. Szabó, *Odd independent transversals are odd*, Combinatorics, Probability and Computing 15 (2006), 193–211. [Author manuscript](https://page.mi.fu-berlin.de/szabo/PDF/oddtransversal.pdf). Theorem 1.1 states the odd threshold; Section 2 supplies feasible pairs and IMCs; Section 3 supplies the cell framework; Theorem 4.1 supplies the bipartite-component switching argument.
