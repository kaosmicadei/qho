# Quantum Harmonic Oscillator
This repo is part of personal journey learning Lean. Here I explore how to 
formalize the quantum harmonic oscillator based on the algebraic properties of 
the ladder operators.

I chose the harmonic oscillator because of its simplicity and fundamental role 
in quantum mechanics.

As a short recap, the harmonic oscillator describes a particle subject to a quadratic potential, which leads to equally spaced energy levels.

The dynamic of the harmonic oscillator is given by the Hamiltonian:
```math
H = \frac{p^2}{2m} + \frac{1}{2}m\omega^2 x^2 
```
with the canonical commutation relation
```math
[x,p] = i\hbar .
```

The ladder operators, also known as annihilation and creation operators, are defined as:
```math
a = \sqrt{\frac{m\omega}{2\hbar}} \left( x + \frac{i}{m\omega} p \right)
, \quad
a^\dagger = \sqrt{\frac{m\omega}{2\hbar}} \left( x - \frac{i}{m\omega} p \right)
```
such that $`x \propto \left(a + a^\dagger \right)`$ and $`p \propto \left(a - a^\dagger \right)`$.

Defining $`N = a^\dagger a`$, we can rewrite the Hamiltonian as:
```math
H = \hbar \omega \left(N + \frac{1}{2}\right)
```

Finding the Hamiltonian eigenstates is the same as finding the eigenstates of the number operator $`N`$. That means, if $`|\psi\rangle`$ is an eigenstate of $`N`$ with eigenvalue $`c`$, then it is also an eigenstate of the Hamiltonian with eigenvalue $`\hbar \omega (c + \frac{1}{2})`$.

The goal here is to prove that $`c`$ must be a non-negative integer. Therefore,
the energy levels of the harmonic oscillator are quantized (discrete) and given by 
```math
E_n = \hbar \omega \left(n + \frac{1}{2}\right), \quad n \in \mathbb{N} .
```

To do so, we will need the following commutation relations:
* $`[a, a^\dagger] = 1`$
* $`[N, a] = -a`$
* $`[N, a^\dagger] = a^\dagger`$

From that, we can prove that, if $`N|\psi\rangle = c|\psi\rangle`$, then
* $`N(a|\psi\rangle) = (c-1)(a|\psi\rangle)`$
* $`N(a^\dagger|\psi\rangle) = (c+1)(a^\dagger|\psi\rangle)`$

from which we can derive that successive application of $`a`$ or $`a^\dagger`$ move the eigenvalue $`c`$ down or up by 1, respectively,
```math
N(a^n|\psi\rangle) = (c-n)(a^n|\psi\rangle) .
```

Since
$`\langle\psi|N|\psi\rangle = \langle\psi|a^\dagger a|\psi\rangle = \|a|\psi\rangle\|^2 \ge 0`$ and $`\langle\psi|N|\psi\rangle = c\langle\psi|\psi\rangle`$,
we must have $`c \ge 0`$. So, there must exist a ground state
$`|\psi_0\rangle`$ such that $`a|\psi_0\rangle = 0`$.

Therefore, if $`c \ge 0`$ and applying $`a`$ and $`a^\dagger`$ repeatedly can 
only move $`c`$ by 1, then $`c`$ must be a non-negative integer, 
$`c \in \mathbb{N}`$.

Finally, we can construct all eigenstates of the number operator $`N`$ by
applying $`a^\dagger`$ repeatedly to the ground state $`|0\rangle`$.

Let $`|n\rangle`$ denote the eigenstate of $`N`$ with eigenvalue $`n`$
and $`|0\rangle`$ is the ground state satisfying $`a|0\rangle = 0`$, the eigenstates $`|n\rangle`$ can be constructed as
```math
|n\rangle = \frac{(a^\dagger)^n}{\sqrt{n!}}|0\rangle.
```

Looking back at the Hamiltonian, we find that
```math
H|n\rangle = \hbar \omega \left(n + \frac{1}{2}\right)|n\rangle ,
```
which confirms that the energy levels are quantized and given by $`E_n = \hbar \omega \left(n + \frac{1}{2}\right)`$. And, in particular, the ground state energy is $`E_0 = \frac{1}{2} \hbar \omega`$ known as the **zero-point energy**.