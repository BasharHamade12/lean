

Let a discrete-time linear time-invariant (LTI) system be given by the state-space model:
\[
\mathbf{x}(k+1) = \mathbf{A}\mathbf{x}(k) + \mathbf{B}\mathbf{u}(k),
\]
where:
- \(\mathbf{x}(k) \in \mathbb{R}^n\) is the state vector at time step \(k\),
- \(\mathbf{u}(k) \in \mathbb{R}^p\) is the input vector,
- \(\mathbf{A} \in \mathbb{R}^{n \times n}\) is the state matrix,
- \(\mathbf{B} \in \mathbb{R}^{n \times p}\) is the input matrix.

Given \(\mathbf{u}(k) = \mathbf{0} \; \forall k \geq 0\), we have the following equivalence:
\[
|\lambda_i(\mathbf{A})| < 1 \; \forall i \in \{1, 2, \dots, n\} \quad \Leftrightarrow \quad \lim_{k \to \infty} \|\mathbf{x}(k)\| = 0.
\]

---





**Claim:**  
If \(\mathbf{u}(k) = \mathbf{0}\) and \(|\lambda_i(\mathbf{A})| < 1\) for all \(i\), then \(\lim_{k \to \infty} \|\mathbf{x}(k)\| = 0\).




**Proof:**

  
given $|\lambda_i(\mathbf{A})| < 1$ $\implies$ $\rho(\mathbf{A}) < 1$.


From Gelfand's formula, we have:
$$\lim_{k \to \infty} \|\mathbf{A}^k\|^{1/k} = \rho(\mathbf{A})$$
Since we know $\rho(\mathbf{A}) < 1$, let's choose a real number $r$ such that $\rho(\mathbf{A}) < r < 1$. Such a number must exist.


$\implies \|\mathbf{A}^k\|^{1/k} < r \ \ \ \ \ \ \ \ \forall k > some \ N$


$ \implies \|\mathbf{A}^k\| < r^k \quad \text{for all } k > N $


but $\lim_{k \to \infty} r^k = 0$ and $0 \le \|\mathbf{A}^k\| < r^k$
    
By the Squeeze Theorem, as the upper and lower bounds both go to zero, the term in the middle must also go to zero:
 $$\lim_{k \to \infty} \|\mathbf{A}^k\| = 0$$


we have $\mathbf{x}(k) = \mathbf{A}^k \mathbf{x}(0)  \implies$ 
    $0 \le \|\mathbf{x}(k)\| = \|\mathbf{A}^k \mathbf{x}(0)\| \le \|\mathbf{A}^k\| \|\mathbf{x}(0)\|$
    Taking the limit as $k \to \infty$:
    $\lim_{k \to \infty} \|\mathbf{x}(k)\| \le \left(\lim_{k \to \infty} \|\mathbf{A}^k\|\right) \|\mathbf{x}(0)\| = 0 \cdot \|\mathbf{x}(0)\| = 0$
    Again, by the Squeeze Theorem, since $\|\mathbf{x}(k)\|$ is bounded below by 0 and its upper bound approaches 0, we conclude:
    $$\lim_{k \to \infty} \|\mathbf{x}(k)\| = 0$$

