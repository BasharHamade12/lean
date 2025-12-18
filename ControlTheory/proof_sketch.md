

## Direct Proof of Necessity

**Theorem:** If the discrete-time system \(x(k+1) = Ax(k) + Bu(k)\) is completely reachable, then \(\text{rank}(\mathcal{C}) = n\).

### Step 1: Characterize the Reachable Set Explicitly

Starting from \(x(0) = 0\), the state at time \(k\) is given by direct iteration:

\[
x(k) = \sum_{j=0}^{k-1} A^{k-1-j}Bu(j)
\]

This can be written as:

\[
x(k) = \begin{bmatrix} A^{k-1}B & A^{k-2}B & \cdots & B \end{bmatrix} \begin{bmatrix} u(0) \\ u(1) \\ \vdots \\ u(k-1) \end{bmatrix}
\]

Therefore, the set of states reachable in exactly \(k\) steps is:

\[
\mathcal{R}_k = \text{Range}(\mathcal{C}_k) = \text{Im}(\mathcal{C}_k)
\]

where \(\mathcal{C}_k = [A^{k-1}B \mid \cdots \mid B]\).

### Step 2: Apply Cayley-Hamilton to Establish Finite Dimension

By the Cayley-Hamilton theorem, \(A^n\) can be expressed as a linear combination of \(I, A, \ldots, A^{n-1}\). Therefore, for any \(j \geq n\):

\[
A^j B \in \text{span}\{B, AB, \ldots, A^{n-1}B\}
\]

This directly implies:

\[
\text{Range}(\mathcal{C}_k) \subseteq \text{Range}(\mathcal{C}_n) = \text{Range}(\mathcal{C}) \quad \text{for all } k \geq 1
\]

Conversely, since \(\mathcal{C} = \mathcal{C}_n\) is formed from columns of various \(\mathcal{C}_k\), we have \(\text{Range}(\mathcal{C}) \subseteq \bigcup_{k \geq 1} \text{Range}(\mathcal{C}_k)\).

Therefore, the total reachable set is exactly:

\[
\mathcal{R} = \bigcup_{k=1}^{\infty} \mathcal{R}_k = \text{Range}(\mathcal{C})
\]

### Step 3: Apply the Definition of Complete Reachability

By the definition of complete reachability, **every** state \(x \in \mathbb{R}^n\) is reachable from the origin. This means:

\[
\mathcal{R} = \mathbb{R}^n
\]

### Step 4: Conclude the Rank Condition

From Steps 2 and 3:

\[
\text{Range}(\mathcal{C}) = \mathcal{R} = \mathbb{R}^n
\]

By the fundamental property of matrix rank, the range of a matrix equals the entire space \(\mathbb{R}^n\) if and only if the matrix has full row rank. Since \(\mathcal{C}\) is an \(n \times nm\) matrix:

\[
\text{Range}(\mathcal{C}) = \mathbb{R}^n \quad \Longleftrightarrow \quad \text{rank}(\mathcal{C}) = n
\]

Therefore, \(\text{rank}(\mathcal{C}) = n\). ∎


